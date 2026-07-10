import Percolation.Critical.ExponentialDecay

/-!
# Menshikov's recursive bootstrap

This file formalizes Grimmett's proof of Lemma 5.24, equations (5.27)--(5.35).  The density
decrement and radius multiplier below are exactly the quantities used in the book.  In
particular, this argument depends only on the master inequality (5.22) and on
`g_p(n) → 0` below the critical point; it does not use susceptibility or exponential decay.
-/

namespace Percolation

open Filter MeasureTheory
open scoped unitInterval BigOperators

/-- The density decrement in Grimmett (5.30) and (5.32). -/
noncomputable def menshikovDecrement (x : ℝ) : ℝ :=
  3 * x * (1 - Real.log x)

/-- The integer radius multiplier in Grimmett (5.28) and (5.32). -/
noncomputable def menshikovMultiplier (x : ℝ) : ℕ :=
  ⌊x⁻¹⌋₊

lemma menshikovDecrement_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < menshikovDecrement x := by
  unfold menshikovDecrement
  have hlog : Real.log x < 0 := Real.log_neg hx0 hx1
  exact mul_pos (mul_pos (by norm_num) hx0) (by linarith)

/-- The elementary majorant used to control the total density loss in the recursion.
It is a convenient quantitative version of the convergence assertion following (5.33). -/
lemma menshikovDecrement_le_nine_mul_sqrt {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    menshikovDecrement x ≤ 9 * Real.sqrt x := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlogs : -((Real.sqrt x) ⁻¹) ≤ Real.log (Real.sqrt x) :=
    Real.neg_inv_le_log hs0.le
  have hlogeq : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]
    ring
  have hlogLower : -(2 * (Real.sqrt x) ⁻¹) ≤ Real.log x := by
    rw [hlogeq]
    linarith
  have hsle : Real.sqrt x ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hx1
  have hxsqrt : x ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx0.le]
  have hcancel : x * (Real.sqrt x) ⁻¹ = Real.sqrt x := by
    rw [← div_eq_mul_inv, Real.div_sqrt]
  unfold menshikovDecrement
  calc
    3 * x * (1 - Real.log x) ≤ 3 * x * (1 + 2 * (Real.sqrt x) ⁻¹) := by
      gcongr
      linarith
    _ = 3 * x + 6 * (x * (Real.sqrt x) ⁻¹) := by ring
    _ = 3 * x + 6 * Real.sqrt x := by rw [hcancel]
    _ ≤ 9 * Real.sqrt x := by linarith

lemma two_le_menshikovMultiplier {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4) :
    2 ≤ menshikovMultiplier x := by
  unfold menshikovMultiplier
  apply (Nat.le_floor_iff' (by omega : (2 : ℕ) ≠ 0)).2
  change (2 : ℝ) ≤ x⁻¹
  rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2) hx0]
  linarith

lemma menshikovMultiplier_cast_le_inv {x : ℝ} (hx0 : 0 < x) :
    (menshikovMultiplier x : ℝ) ≤ x⁻¹ := by
  exact Nat.floor_le (inv_nonneg.mpr hx0.le)

/-- The partial-sum estimate between (5.27) and (5.28). -/
lemma radiusTailPartialSum_mul_multiplier_le
    (d : ℕ) (q : I) {n : ℕ} (hn : 1 ≤ n)
    (hg0 : 0 < radiusTail d q n) (hg : radiusTail d q n ≤ 1 / 4) :
    radiusTailPartialSum d q (n * menshikovMultiplier (radiusTail d q n)) ≤
      3 * (n * menshikovMultiplier (radiusTail d q n) : ℕ) * radiusTail d q n := by
  let g := radiusTail d q n
  let γ := menshikovMultiplier g
  let N := n * γ
  have hγ : 2 ≤ γ := two_le_menshikovMultiplier hg0 hg
  have hnN : n ≤ N := by
    dsimp [N]
    exact Nat.le_mul_of_pos_right n (by omega)
  have hnN1 : n ≤ N + 1 := hnN.trans (Nat.le_succ _)
  have hg_nonneg : 0 ≤ g := hg0.le
  have hfirst : (∑ i ∈ Finset.range n, radiusTail d q i) ≤ n := by
    calc
      (∑ i ∈ Finset.range n, radiusTail d q i) ≤
          ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact measureReal_le_one
      _ = n := by simp
  have hsecond : (∑ i ∈ Finset.Ico n (N + 1), radiusTail d q i) ≤ N * g := by
    calc
      (∑ i ∈ Finset.Ico n (N + 1), radiusTail d q i) ≤
          ∑ _i ∈ Finset.Ico n (N + 1), g := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : n ≤ i := (by simpa using hi : n ≤ i ∧ i ≤ N).1
        exact radiusTail_antitone d q hi'
      _ = ((N + 1 - n : ℕ) : ℝ) * g := by simp [Nat.card_Ico]
      _ ≤ N * g := by
        gcongr
        omega
  have hn_le_twoNg : (n : ℝ) ≤ 2 * N * g := by
    have hfloor : (γ : ℝ) ≥ g⁻¹ - 1 := by
      have hlt := Nat.lt_floor_add_one (g⁻¹)
      dsimp [γ, menshikovMultiplier]
      exact_mod_cast (le_of_lt (sub_lt_iff_lt_add.mpr hlt))
    have hinv : 1 ≤ 2 * g * (γ : ℝ) := by
      have hgquarter : g ≤ 1 / 4 := hg
      have hmul := mul_le_mul_of_nonneg_left hfloor hg_nonneg
      rw [mul_sub, mul_inv_cancel₀ hg0.ne', mul_one] at hmul
      nlinarith
    have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [N]
    push_cast
    nlinarith
  rw [radiusTailPartialSum]
  rw [← Finset.sum_range_add_sum_Ico _ hnN1]
  dsimp [N, g, γ] at *
  nlinarith

/-- The basic squaring step (5.29)--(5.31). -/
theorem radiusTail_menshikov_recursion_step
    {d n : ℕ} {q q' : I} (hd : 0 < d) (hn : 1 ≤ n)
    (hg0 : 0 < radiusTail d q n) (hg : radiusTail d q n ≤ 1 / 4)
    (hdec : (q : ℝ) - (q' : ℝ) = menshikovDecrement (radiusTail d q n))
    (hq'0 : 0 < (q' : ℝ)) (hqq' : q' ≤ q) (hq1 : (q : ℝ) < 1)
    (hdecOne : menshikovDecrement (radiusTail d q n) ≤ 1) :
    radiusTail d q' (n * menshikovMultiplier (radiusTail d q n)) ≤
      (radiusTail d q n) ^ 2 := by
  let g := radiusTail d q n
  let N := n * menshikovMultiplier g
  have hsum := radiusTailPartialSum_mul_multiplier_le d q hn hg0 hg
  have hsumPos := radiusTailPartialSum_pos d q N
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.mul_pos hn (lt_of_lt_of_le (by omega) (two_le_menshikovMultiplier hg0 hg))
  have hdenPos : 0 < 3 * (N : ℝ) * g := by positivity
  have hsum' : radiusTailPartialSum d q N ≤ 3 * (N : ℝ) * g := by
    simpa [N, g] using hsum
  have hratio : (3 * (N : ℝ) * g) ⁻¹ ≤
      (radiusTailPartialSum d q N) ⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hsumPos hsum'
  have hfrac : (3 * g) ⁻¹ ≤ (N : ℝ) / radiusTailPartialSum d q N := by
    have := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ N by positivity)
    field_simp [hg0.ne', (show (N : ℝ) ≠ 0 by positivity)] at this ⊢
    nlinarith
  have hmaster := radiusTail_master_inequality (d := d) (n := N)
    (α := q') (β := q) hd hq'0 (by exact_mod_cast hqq') hq1
  have hqTail : radiusTail d q N ≤ g := radiusTail_antitone d q (by
    dsimp [N]
    exact Nat.le_mul_of_pos_right n
      (lt_of_lt_of_le (by omega) (two_le_menshikovMultiplier hg0 hg)))
  have hlog : Real.exp (Real.log g) = g := Real.exp_log hg0
  have hexponent :
      -(((q : ℝ) - (q' : ℝ)) *
          ((N : ℝ) / radiusTailPartialSum d q N - 1)) ≤ Real.log g := by
    rw [hdec]
    have hdec0 : 0 ≤ menshikovDecrement g :=
      (menshikovDecrement_pos hg0 (hg.trans_lt (by norm_num))).le
    have hmul := mul_le_mul_of_nonneg_left hfrac hdec0
    have hquot : menshikovDecrement g * (3 * g)⁻¹ = 1 - Real.log g := by
      calc
        menshikovDecrement g * (3 * g)⁻¹ =
            (3 * 3⁻¹) * (g * g⁻¹) * (1 - Real.log g) := by
          simp only [menshikovDecrement, mul_inv_rev]
          ring
        _ = 1 - Real.log g := by rw [mul_inv_cancel₀ hg0.ne']; simp
    calc
      -(menshikovDecrement g *
          ((N : ℝ) / radiusTailPartialSum d q N - 1)) =
          menshikovDecrement g -
            menshikovDecrement g * ((N : ℝ) / radiusTailPartialSum d q N) := by ring
      _ ≤ menshikovDecrement g - menshikovDecrement g * (3 * g)⁻¹ := by
        exact sub_le_sub_left hmul _
      _ = menshikovDecrement g - (1 - Real.log g) := by rw [hquot]
      _ ≤ 1 - (1 - Real.log g) := sub_le_sub_right hdecOne _
      _ = Real.log g := by ring
  calc
    radiusTail d q' N ≤ radiusTail d q N *
        Real.exp (-(((q : ℝ) - (q' : ℝ)) *
          ((N : ℝ) / radiusTailPartialSum d q N - 1))) := hmaster
    _ ≤ g * Real.exp (Real.log g) :=
      mul_le_mul hqTail (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le hg0.le
    _ = g ^ 2 := by rw [hlog]; ring

/-! ### The iterated recursion (5.32)--(5.35) -/

/-- The pair `(p_i,n_i)` in (5.32).  Projection to the unit interval makes this a total
definition; the invariant theorem below proves that projection never changes the recursively
computed density. -/
noncomputable def menshikovState (d : ℕ) (q₀ : I) (n₀ : ℕ) : ℕ → I × ℕ
  | 0 => (q₀, n₀)
  | i + 1 =>
      let s := menshikovState d q₀ n₀ i
      let g := radiusTail d s.1 s.2
      (Set.projIcc 0 1 zero_le_one ((s.1 : ℝ) - menshikovDecrement g),
        s.2 * menshikovMultiplier g)

noncomputable def menshikovDensity (d : ℕ) (q₀ : I) (n₀ i : ℕ) : I :=
  (menshikovState d q₀ n₀ i).1

noncomputable def menshikovRadius (d : ℕ) (q₀ : I) (n₀ i : ℕ) : ℕ :=
  (menshikovState d q₀ n₀ i).2

noncomputable def menshikovTail (d : ℕ) (q₀ : I) (n₀ i : ℕ) : ℝ :=
  radiusTail d (menshikovDensity d q₀ n₀ i) (menshikovRadius d q₀ n₀ i)

@[simp] lemma menshikovDensity_zero (d : ℕ) (q₀ : I) (n₀ : ℕ) :
    menshikovDensity d q₀ n₀ 0 = q₀ := rfl

@[simp] lemma menshikovRadius_zero (d : ℕ) (q₀ : I) (n₀ : ℕ) :
    menshikovRadius d q₀ n₀ 0 = n₀ := rfl

@[simp] lemma menshikovTail_zero (d : ℕ) (q₀ : I) (n₀ : ℕ) :
    menshikovTail d q₀ n₀ 0 = radiusTail d q₀ n₀ := rfl

lemma menshikovDensity_succ (d : ℕ) (q₀ : I) (n₀ i : ℕ) :
    menshikovDensity d q₀ n₀ (i + 1) =
      Set.projIcc 0 1 zero_le_one
        ((menshikovDensity d q₀ n₀ i : ℝ) - menshikovDecrement (menshikovTail d q₀ n₀ i)) := by
  rfl

lemma menshikovRadius_succ (d : ℕ) (q₀ : I) (n₀ i : ℕ) :
    menshikovRadius d q₀ n₀ (i + 1) =
      menshikovRadius d q₀ n₀ i * menshikovMultiplier (menshikovTail d q₀ n₀ i) := by
  rfl

/-- Simultaneous invariants of Grimmett's recursion. -/
structure MenshikovInvariants (d : ℕ) (p q₀ : I) (n₀ i : ℕ) : Prop where
  density_le : menshikovDensity d q₀ n₀ i ≤ q₀
  density_loss_le :
    (q₀ : ℝ) - (menshikovDensity d q₀ n₀ i : ℝ) ≤
      18 * Real.sqrt (radiusTail d q₀ n₀) * (1 - (1 / 2 : ℝ) ^ i)
  target_lt_density : p < menshikovDensity d q₀ n₀ i
  radius_pos : 0 < menshikovRadius d q₀ n₀ i
  tail_pos : 0 < menshikovTail d q₀ n₀ i
  tail_le_quarter : menshikovTail d q₀ n₀ i ≤ 1 / 4
  sqrt_tail_le :
    Real.sqrt (menshikovTail d q₀ n₀ i) ≤
      (1 / 2 : ℝ) ^ i * Real.sqrt (radiusTail d q₀ n₀)
  tail_mul_radius_le :
    menshikovTail d q₀ n₀ i * menshikovRadius d q₀ n₀ i ≤
      radiusTail d q₀ n₀ * n₀
  radius_growth : n₀ * 2 ^ i ≤ menshikovRadius d q₀ n₀ i

/-- The source recursion is valid at every stage and retains all quantitative invariants
needed to fill the gaps between the selected radii. -/
theorem menshikov_invariants
    {d n₀ : ℕ} {p q₀ : I} (hd : 0 < d) (hn₀ : 1 ≤ n₀)
    (hpq : p < q₀) (hqpc : (q₀ : ℝ) < cubicCriticalProbability d)
    (hgSmall : radiusTail d q₀ n₀ ≤ 1 / 4)
    (hloss : 18 * Real.sqrt (radiusTail d q₀ n₀) ≤ ((q₀ : ℝ) - (p : ℝ)) / 2) :
    ∀ i, MenshikovInvariants d p q₀ n₀ i := by
  intro i
  induction i with
  | zero =>
      have hg0 : 0 < radiusTail d q₀ n₀ :=
        radiusTail_pos_of_pos_density hd (lt_of_le_of_lt p.2.1 (by exact_mod_cast hpq))
      constructor
      · exact le_rfl
      · simp
      · exact hpq
      · simpa [menshikovRadius_zero] using hn₀
      · exact hg0
      · exact hgSmall
      · simp
      · simp
      · simp
  | succ i ih =>
      let qi := menshikovDensity d q₀ n₀ i
      let ni := menshikovRadius d q₀ n₀ i
      let gi := menshikovTail d q₀ n₀ i
      let raw := (qi : ℝ) - menshikovDecrement gi
      have hgi0 : 0 < gi := ih.tail_pos
      have hgi1 : gi < 1 := ih.tail_le_quarter.trans_lt (by norm_num)
      have hdec0 : 0 < menshikovDecrement gi := menshikovDecrement_pos hgi0 hgi1
      have hsqrt0 : 0 ≤ Real.sqrt (radiusTail d q₀ n₀) := Real.sqrt_nonneg _
      have hpow0 : 0 ≤ (1 / 2 : ℝ) ^ i := by positivity
      have hpow1 : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hdecBound : menshikovDecrement gi ≤
          9 * (1 / 2 : ℝ) ^ i * Real.sqrt (radiusTail d q₀ n₀) := by
        calc
          menshikovDecrement gi ≤ 9 * Real.sqrt gi :=
            menshikovDecrement_le_nine_mul_sqrt hgi0 hgi1.le
          _ ≤ 9 * ((1 / 2 : ℝ) ^ i * Real.sqrt (radiusTail d q₀ n₀)) := by
            gcongr
            exact ih.sqrt_tail_le
          _ = _ := by ring
      have hlossSucc : (q₀ : ℝ) - raw ≤
          18 * Real.sqrt (radiusTail d q₀ n₀) *
            (1 - (1 / 2 : ℝ) ^ (i + 1)) := by
        have h := add_le_add ih.density_loss_le hdecBound
        dsimp [raw]
        rw [pow_succ]
        nlinarith
      have htargetRaw : (p : ℝ) < raw := by
        have hhalf : 18 * Real.sqrt (radiusTail d q₀ n₀) ≤
            (q₀ : ℝ) - (p : ℝ) := hloss.trans (half_le_self (sub_nonneg.mpr hpq.le))
        have hstrict :
            18 * Real.sqrt (radiusTail d q₀ n₀) *
                (1 - (1 / 2 : ℝ) ^ (i + 1)) <
              18 * Real.sqrt (radiusTail d q₀ n₀) := by
          have hgbase : 0 < radiusTail d q₀ n₀ := by
            exact radiusTail_pos_of_pos_density hd
              (lt_of_le_of_lt p.2.1 (by exact_mod_cast hpq))
          have hsbase : 0 < Real.sqrt (radiusTail d q₀ n₀) := Real.sqrt_pos.2 hgbase
          have hpw : 0 < (1 / 2 : ℝ) ^ (i + 1) := by positivity
          nlinarith
        linarith
      have hraw0 : 0 ≤ raw := le_trans p.2.1 htargetRaw.le
      have hraw1 : raw ≤ 1 := by
        dsimp [raw]
        exact (sub_le_self (qi : ℝ) hdec0.le).trans qi.2.2
      have hproj : Set.projIcc 0 1 zero_le_one raw = ⟨raw, hraw0, hraw1⟩ :=
        Set.projIcc_of_mem zero_le_one ⟨hraw0, hraw1⟩
      have hqsuccVal : (menshikovDensity d q₀ n₀ (i + 1) : ℝ) = raw := by
        rw [menshikovDensity_succ]
        exact congrArg Subtype.val hproj
      have hqsuccLeQi : menshikovDensity d q₀ n₀ (i + 1) ≤ qi := by
        change (menshikovDensity d q₀ n₀ (i + 1) : ℝ) ≤ (qi : ℝ)
        rw [hqsuccVal]
        dsimp [raw]
        linarith
      have hqsuccPos : 0 < (menshikovDensity d q₀ n₀ (i + 1) : ℝ) := by
        rw [hqsuccVal]
        exact lt_of_le_of_lt p.2.1 htargetRaw
      have hqiltOne : (qi : ℝ) < 1 := by
        have hqiLe : (qi : ℝ) ≤ (q₀ : ℝ) := by exact_mod_cast ih.density_le
        exact hqiLe.trans_lt (hqpc.trans_le (cubicCriticalProbability_le_one d))
      have hdecOne : menshikovDecrement gi ≤ 1 := by
        calc
          menshikovDecrement gi ≤
              9 * (1 / 2 : ℝ) ^ i * Real.sqrt (radiusTail d q₀ n₀) := hdecBound
          _ ≤ 9 * Real.sqrt (radiusTail d q₀ n₀) := by
            exact mul_le_mul_of_nonneg_right (by nlinarith [hpow1]) hsqrt0
          _ ≤ 1 := by
            have := hloss
            have hgap : (q₀ : ℝ) - (p : ℝ) ≤ 1 := by
              linarith [q₀.2.2, p.2.1]
            nlinarith
      have hsq := radiusTail_menshikov_recursion_step (d := d) (n := ni)
        (q := qi) (q' := menshikovDensity d q₀ n₀ (i + 1)) hd ih.radius_pos
        hgi0 ih.tail_le_quarter (by
          rw [hqsuccVal]
          dsimp [raw, gi, menshikovTail, qi, ni]
          ring) hqsuccPos hqsuccLeQi hqiltOne hdecOne
      have hnSucc : menshikovRadius d q₀ n₀ (i + 1) =
          ni * menshikovMultiplier gi := menshikovRadius_succ d q₀ n₀ i
      have hgSuccLe : menshikovTail d q₀ n₀ (i + 1) ≤ gi ^ 2 := by
        simpa [menshikovTail, qi, ni, gi, hnSucc] using hsq
      have htargetSucc : p < menshikovDensity d q₀ n₀ (i + 1) := by
        exact_mod_cast htargetRaw.trans_eq hqsuccVal.symm
      have hgSucc0 : 0 < menshikovTail d q₀ n₀ (i + 1) :=
        radiusTail_pos_of_pos_density hd hqsuccPos
      have hmultTwo : 2 ≤ menshikovMultiplier gi :=
        two_le_menshikovMultiplier hgi0 ih.tail_le_quarter
      have hnSuccPos : 0 < menshikovRadius d q₀ n₀ (i + 1) := by
        rw [hnSucc]
        exact Nat.mul_pos ih.radius_pos (by omega)
      have hsqrtSuccLe : Real.sqrt (menshikovTail d q₀ n₀ (i + 1)) ≤ gi := by
        have := Real.sqrt_le_sqrt hgSuccLe
        simpa [Real.sqrt_sq hgi0.le] using this
      have hgisqrt : gi ≤ (1 / 2 : ℝ) * Real.sqrt gi := by
        have hsle : Real.sqrt gi ≤ 1 / 2 := by
          rw [Real.sqrt_le_iff]
          constructor <;> nlinarith [Real.sq_sqrt hgi0.le, ih.tail_le_quarter]
        calc
          gi = Real.sqrt gi * Real.sqrt gi := (Real.mul_self_sqrt hgi0.le).symm
          _ ≤ Real.sqrt gi * (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hsle (Real.sqrt_nonneg _)
          _ = (1 / 2 : ℝ) * Real.sqrt gi := by ring
      have hsqrtBound :
          Real.sqrt (menshikovTail d q₀ n₀ (i + 1)) ≤
            (1 / 2 : ℝ) ^ (i + 1) * Real.sqrt (radiusTail d q₀ n₀) := by
        calc
          Real.sqrt (menshikovTail d q₀ n₀ (i + 1)) ≤ gi := hsqrtSuccLe
          _ ≤ (1 / 2 : ℝ) * Real.sqrt gi := hgisqrt
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ i *
              Real.sqrt (radiusTail d q₀ n₀)) := by gcongr; exact ih.sqrt_tail_le
          _ = _ := by rw [pow_succ]; ring
      have hproduct : menshikovTail d q₀ n₀ (i + 1) *
          menshikovRadius d q₀ n₀ (i + 1) ≤ radiusTail d q₀ n₀ * n₀ := by
        have hmultInv := menshikovMultiplier_cast_le_inv hgi0
        have hstep : menshikovTail d q₀ n₀ (i + 1) *
            menshikovRadius d q₀ n₀ (i + 1) ≤ gi * ni := by
          rw [hnSucc]
          push_cast
          calc
            menshikovTail d q₀ n₀ (i + 1) *
                ((ni : ℝ) * menshikovMultiplier gi) ≤
                gi ^ 2 * ((ni : ℝ) * menshikovMultiplier gi) := by gcongr
            _ ≤ gi ^ 2 * ((ni : ℝ) * gi⁻¹) := by gcongr
            _ = gi * ni := by field_simp [hgi0.ne']
        exact hstep.trans ih.tail_mul_radius_le
      constructor
      · exact hqsuccLeQi.trans ih.density_le
      · rw [hqsuccVal]
        exact hlossSucc
      · exact htargetSucc
      · exact hnSuccPos
      · exact hgSucc0
      · calc
          menshikovTail d q₀ n₀ (i + 1) ≤ gi ^ 2 := hgSuccLe
          _ ≤ 1 / 4 := by nlinarith [hgi0, ih.tail_le_quarter]
      · exact hsqrtBound
      · exact hproduct
      · rw [hnSucc, pow_succ]
        nlinarith [ih.radius_growth, hmultTwo]

/-- The selected-radius estimate (5.35), converted into the all-radius
inverse-square-root bound by Grimmett's gap-filling argument. -/
theorem radiusTail_le_inv_sqrt_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n : ℕ, 1 ≤ n →
      radiusTail d p n ≤ delta / Real.sqrt n := by
  have hd0 : 0 < d := by omega
  let qr : ℝ := ((p : ℝ) + cubicCriticalProbability d) / 2
  have hpqr : (p : ℝ) < qr := by dsimp [qr]; linarith
  have hqrpc : qr < cubicCriticalProbability d := by dsimp [qr]; linarith
  have hqr0 : 0 ≤ qr := p.2.1.trans hpqr.le
  have hqr1 : qr ≤ 1 :=
    hqrpc.le.trans (cubicCriticalProbability_le_one d)
  let q₀ : I := ⟨qr, hqr0, hqr1⟩
  have hpq : p < q₀ := by exact_mod_cast hpqr
  have hqpc : (q₀ : ℝ) < cubicCriticalProbability d := hqrpc
  let gap : ℝ := (q₀ : ℝ) - (p : ℝ)
  have hgap : 0 < gap := sub_pos.mpr (by exact_mod_cast hpq)
  let ε : ℝ := min (1 / 4) ((gap / 36) ^ 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (sq_pos_of_pos (div_pos hgap (by norm_num)))
  have htheta : theta d q₀ = 0 := theta_eq_zero_of_lt_criticalProbability hqpc
  have htend : Tendsto (radiusTail d q₀) atTop (nhds 0) := by
    simpa [htheta] using radiusTail_tendsto_theta d q₀
  have hevent : ∀ᶠ n : ℕ in atTop, radiusTail d q₀ n < ε :=
    htend (Iio_mem_nhds hε)
  obtain ⟨n₀, hn₀, hn₀small⟩ :=
    (hevent.and (eventually_ge_atTop (1 : ℕ))).exists
  have hgSmall : radiusTail d q₀ n₀ ≤ 1 / 4 :=
    (hn₀.trans_le (min_le_left _ _)).le
  have hgSquare : radiusTail d q₀ n₀ ≤ (gap / 36) ^ 2 :=
    (hn₀.trans_le (min_le_right _ _)).le
  have hsqrtSmall : Real.sqrt (radiusTail d q₀ n₀) ≤ gap / 36 := by
    have hs := Real.sqrt_le_sqrt hgSquare
    rw [Real.sqrt_sq (div_nonneg hgap.le (by norm_num))] at hs
    exact hs
  have hloss : 18 * Real.sqrt (radiusTail d q₀ n₀) ≤ gap / 2 := by
    nlinarith
  have hinv := menshikov_invariants (d := d) (n₀ := n₀) (p := p) (q₀ := q₀)
    hd0 hn₀small hpq hqpc hgSmall hloss
  refine ⟨Real.sqrt n₀, Real.sqrt_pos.2 (by exact_mod_cast hn₀small), ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtnPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  by_cases hnn₀ : n ≤ n₀
  · have hsqrtLe : Real.sqrt n ≤ Real.sqrt n₀ := Real.sqrt_le_sqrt (by exact_mod_cast hnn₀)
    have hone : (1 : ℝ) ≤ Real.sqrt n₀ / Real.sqrt n := by
      exact (le_div_iff₀ hsqrtnPos).2 (by simpa using hsqrtLe)
    exact measureReal_le_one.trans hone
  · have hn₀n : n₀ < n := Nat.lt_of_not_ge hnn₀
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt n (by omega : (1 : ℕ) < 2)
    have hpowLe : 2 ^ K ≤ n₀ * 2 ^ K := by
      exact Nat.le_mul_of_pos_left _ hn₀small
    have hexists : ∃ k : ℕ, n < menshikovRadius d q₀ n₀ k := by
      refine ⟨K, hK.trans_le (hpowLe.trans (hinv K).radius_growth)⟩
    let k := Nat.find hexists
    have hkSpec : n < menshikovRadius d q₀ n₀ k := Nat.find_spec hexists
    have hk0 : k ≠ 0 := by
      intro hk
      have hkSpec' : n < n₀ := by simpa [k, hk] using hkSpec
      omega
    obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hkSpec' : n < menshikovRadius d q₀ n₀ (j + 1) := by
      simpa [hjk] using hkSpec
    have hprev : menshikovRadius d q₀ n₀ j ≤ n := by
      apply le_of_not_gt
      apply Nat.find_min hexists
      dsimp [k] at hjk
      omega
    let qj := menshikovDensity d q₀ n₀ j
    let nj := menshikovRadius d q₀ n₀ j
    let gj := menshikovTail d q₀ n₀ j
    have hj := hinv j
    have hpn : radiusTail d p n ≤ gj := by
      calc
        radiusTail d p n ≤ radiusTail d qj n :=
          radiusTail_mono_density d n hj.target_lt_density.le
        _ ≤ radiusTail d qj nj := radiusTail_antitone d qj hprev
        _ = gj := rfl
    have hmultInv := menshikovMultiplier_cast_le_inv hj.tail_pos
    have hselected : gj ^ 2 * menshikovRadius d q₀ n₀ (j + 1) ≤
        radiusTail d q₀ n₀ * n₀ := by
      rw [menshikovRadius_succ]
      push_cast
      calc
        gj ^ 2 * ((nj : ℝ) * menshikovMultiplier gj) ≤
            gj ^ 2 * ((nj : ℝ) * gj⁻¹) := by gcongr
        _ = gj * nj := by field_simp [hj.tail_pos.ne']
        _ ≤ radiusTail d q₀ n₀ * n₀ := hj.tail_mul_radius_le
    have hgbaseOne : radiusTail d q₀ n₀ ≤ 1 := measureReal_le_one
    have hsquareMul : gj ^ 2 * (n : ℝ) ≤ (n₀ : ℝ) := by
      have hnreal : (n : ℝ) ≤ menshikovRadius d q₀ n₀ (j + 1) := by
        exact_mod_cast hkSpec'.le
      calc
        gj ^ 2 * (n : ℝ) ≤ gj ^ 2 * menshikovRadius d q₀ n₀ (j + 1) := by gcongr
        _ ≤ radiusTail d q₀ n₀ * n₀ := hselected
        _ ≤ n₀ := by
          have hn₀nonneg : (0 : ℝ) ≤ n₀ := by positivity
          nlinarith
    have hsquare : gj ^ 2 ≤ (n₀ : ℝ) / n := by
      exact (le_div_iff₀ hnpos).2 (by simpa [mul_comm] using hsquareMul)
    have hsqrt := Real.sqrt_le_sqrt hsquare
    have hgj0 : 0 ≤ gj := hj.tail_pos.le
    have hfinal : gj ≤ Real.sqrt n₀ / Real.sqrt n := by
      simpa [Real.sqrt_sq hgj0, Real.sqrt_div (show (0 : ℝ) ≤ n₀ by positivity)] using hsqrt
    exact hpn.trans hfinal

#print axioms radiusTail_menshikov_recursion_step
#print axioms radiusTail_le_inv_sqrt_of_lt_critical

end Percolation
