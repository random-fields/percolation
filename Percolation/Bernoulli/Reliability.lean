import Percolation.Bernoulli.Russo
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

/-!
# Finite reliability identities

This file starts the reliability-theory part of Grimmett's Chapter 2.  The first
target is the finite-cube form of Theorem (2.34): the derivative of a finite event
probability can be rewritten as a covariance with the number of open coordinates.
-/

namespace Percolation

open scoped BigOperators

/-- The number of open coordinates in a finite-cube configuration, as a real-valued observable. -/
def finiteOpenCount {ι : Type*} (s : Finset ι) : ℝ :=
  s.card

@[simp]
theorem finiteOpenCount_empty {ι : Type*} :
    finiteOpenCount (∅ : Finset ι) = 0 := by
  simp [finiteOpenCount]

theorem finiteOpenCount_insert_of_notMem {ι : Type*} [DecidableEq ι]
    {a : ι} {s : Finset ι} (ha : a ∉ s) :
    finiteOpenCount (insert a s) = finiteOpenCount s + 1 := by
  simp [finiteOpenCount, Finset.card_insert_of_notMem ha]

/-- Covariance of two finite-cube observables under the homogeneous Bernoulli measure. -/
noncomputable def finiteBernoulliCovariance {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X Y : Finset ι → ℝ) : ℝ :=
  finiteBernoulliExpectation E p (fun s ↦ X s * Y s) -
    finiteBernoulliExpectation E p X * finiteBernoulliExpectation E p Y

/-- The finite Bernoulli expectation of the number of open coordinates is `p |E|`. -/
theorem finiteBernoulliExpectation_finiteOpenCount {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) :
    finiteBernoulliExpectation E p finiteOpenCount = p * E.card := by
  induction E using Finset.induction with
  | empty =>
      simp [finiteBernoulliExpectation, finiteOpenCount]
  | insert a E ha ih =>
      rw [finiteBernoulliExpectation_insert_split ha]
      have hopen :
          finiteBernoulliExpectation E p (fun s ↦ finiteOpenCount (insert a s)) =
            finiteBernoulliExpectation E p (fun s ↦ finiteOpenCount s + 1) := by
        apply finiteBernoulliExpectation_congr
        intro s hsE
        exact finiteOpenCount_insert_of_notMem (Finset.notMem_mono hsE ha)
      rw [hopen, finiteBernoulliExpectation_add, finiteBernoulliExpectation_const, ih]
      simp [Finset.card_insert_of_notMem ha]
      ring

/-- For the open-count observable, forcing any coordinate open rather than closed changes the
count by exactly one. -/
theorem finiteDifference_finiteOpenCount {ι : Type*} [DecidableEq ι]
    (e : ι) (s : Finset ι) :
    finiteDifference e finiteOpenCount s = 1 := by
  unfold finiteDifference finiteForceOpen finiteForceClosed finiteOpenCount
  by_cases he : e ∈ s
  · rw [Finset.insert_eq_of_mem he, Finset.card_erase_of_mem he]
    have hcardpos : 0 < s.card := Finset.card_pos.mpr ⟨e, he⟩
    have hpos : 1 ≤ s.card := hcardpos
    rw [Nat.cast_sub hpos]
    ring
  · rw [Finset.erase_eq_of_notMem he, Finset.card_insert_of_notMem he]
    rw [Nat.cast_add, Nat.cast_one]
    ring

/-- Expected finite difference of the open-count observable. -/
theorem finiteBernoulliExpectation_finiteDifference_finiteOpenCount {ι : Type*}
    [DecidableEq ι] (E : Finset ι) (p : ℝ) (e : ι) :
    finiteBernoulliExpectation E p (finiteDifference e finiteOpenCount) = 1 := by
  rw [show finiteBernoulliExpectation E p (finiteDifference e finiteOpenCount) =
      finiteBernoulliExpectation E p (fun _ ↦ (1 : ℝ)) by
    apply finiteBernoulliExpectation_congr
    intro s _hsE
    exact finiteDifference_finiteOpenCount e s]
  exact finiteBernoulliExpectation_const E p 1

/-- Squaring an event indicator leaves it unchanged. -/
theorem indicator_mul_self {ι : Type*} (T : Set (Finset ι)) (s : Finset ι) :
    T.indicator (fun _ ↦ (1 : ℝ)) s * T.indicator (fun _ ↦ (1 : ℝ)) s =
      T.indicator (fun _ ↦ (1 : ℝ)) s := by
  by_cases hs : s ∈ T
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

/-- Variance of a finite event indicator is `P(A)(1-P(A))`. -/
theorem finiteBernoulliCovariance_indicator_self {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliCovariance E p
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s)
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) =
      finiteBernoulliEventProbability E p T *
        (1 - finiteBernoulliEventProbability E p T) := by
  unfold finiteBernoulliCovariance finiteBernoulliEventProbability
  rw [show finiteBernoulliExpectation E p
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s *
          T.indicator (fun _ ↦ (1 : ℝ)) s) =
      finiteBernoulliExpectation E p (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) by
    apply finiteBernoulliExpectation_congr
    intro s _hsE
    exact indicator_mul_self T s]
  ring

/-- Covariance is nonnegative for increasing finite-cube observables, by finite FKG. -/
theorem finiteBernoulliCovariance_nonneg_of_increasing {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {X Y : Finset ι → ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hX : IsIncreasingFinsetFunction E X) (hY : IsIncreasingFinsetFunction E Y) :
    0 ≤ finiteBernoulliCovariance E p X Y := by
  unfold finiteBernoulliCovariance
  have h := finiteBernoulliExpectation_fkg hp0 hp1 hX hY
  linarith

/-- Covariance is linear in the left observable under subtraction. -/
theorem finiteBernoulliCovariance_sub_left {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X Y Z : Finset ι → ℝ) :
    finiteBernoulliCovariance E p (fun s ↦ X s - Y s) Z =
      finiteBernoulliCovariance E p X Z - finiteBernoulliCovariance E p Y Z := by
  unfold finiteBernoulliCovariance
  have hprod :
      finiteBernoulliExpectation E p (fun s ↦ (X s - Y s) * Z s) =
        finiteBernoulliExpectation E p (fun s ↦ X s * Z s - Y s * Z s) := by
    apply finiteBernoulliExpectation_congr
    intro s _hsE
    ring
  rw [hprod, finiteBernoulliExpectation_sub, finiteBernoulliExpectation_sub]
  ring

/-- Covariance as the expectation of centered observables. -/
theorem finiteBernoulliCovariance_eq_centered {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X Y : Finset ι → ℝ) :
    finiteBernoulliCovariance E p X Y =
      finiteBernoulliExpectation E p
        (fun s ↦ (X s - finiteBernoulliExpectation E p X) *
          (Y s - finiteBernoulliExpectation E p Y)) := by
  let ex := finiteBernoulliExpectation E p X
  let ey := finiteBernoulliExpectation E p Y
  unfold finiteBernoulliCovariance
  have hcenter :
      finiteBernoulliExpectation E p
          (fun s ↦ (X s - ex) * (Y s - ey)) =
        finiteBernoulliExpectation E p
          (fun s ↦ (X s * Y s - ex * Y s - ey * X s) + ex * ey) := by
    apply finiteBernoulliExpectation_congr
    intro s _hsE
    ring
  rw [hcenter]
  rw [finiteBernoulliExpectation_add]
  rw [finiteBernoulliExpectation_sub]
  rw [finiteBernoulliExpectation_sub]
  rw [finiteBernoulliExpectation_const_mul, finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_const]
  simp [ex, ey]
  ring

/-- Finite Bernoulli Cauchy-Schwarz for expectations on a finite cube. -/
theorem finiteBernoulliExpectation_mul_sq_le_sq_mul_sq {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X Y : Finset ι → ℝ) :
    (finiteBernoulliExpectation E p (fun s ↦ X s * Y s)) ^ 2 ≤
      finiteBernoulliExpectation E p (fun s ↦ X s ^ 2) *
        finiteBernoulliExpectation E p (fun s ↦ Y s ^ 2) := by
  unfold finiteBernoulliExpectation
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul E.powerset ?_ ?_ ?_
  · intro s _hs
    have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have hweight : 0 ≤ p ^ s.card * (1 - p) ^ (E.card - s.card) :=
      mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hq0 _)
    exact mul_nonneg hweight (sq_nonneg (X s))
  · intro s _hs
    have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have hweight : 0 ≤ p ^ s.card * (1 - p) ^ (E.card - s.card) :=
      mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hq0 _)
    exact mul_nonneg hweight (sq_nonneg (Y s))
  · intro s _hs
    let w : ℝ := p ^ s.card * (1 - p) ^ (E.card - s.card)
    change (w * (X s * Y s)) ^ 2 ≤ (w * X s ^ 2) * (w * Y s ^ 2)
    exact le_of_eq (by ring)

/-- Variance as the expectation of the square of the centered observable. -/
theorem finiteBernoulliCovariance_self_eq_centered_sq {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliCovariance E p X X =
      finiteBernoulliExpectation E p
        (fun s ↦ (X s - finiteBernoulliExpectation E p X) ^ 2) := by
  rw [finiteBernoulliCovariance_eq_centered]
  apply finiteBernoulliExpectation_congr
  intro s _hsE
  ring

/-- Variance is nonnegative on the finite Bernoulli cube. -/
theorem finiteBernoulliCovariance_self_nonneg {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : Finset ι → ℝ) :
    0 ≤ finiteBernoulliCovariance E p X X := by
  rw [finiteBernoulliCovariance_self_eq_centered_sq]
  exact finiteBernoulliExpectation_nonneg hp0 hp1 (fun _s _hsE ↦ sq_nonneg _)

/-- Cauchy-Schwarz for finite Bernoulli covariance. -/
theorem finiteBernoulliCovariance_sq_le_mul_self {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X Y : Finset ι → ℝ) :
    (finiteBernoulliCovariance E p X Y) ^ 2 ≤
      finiteBernoulliCovariance E p X X * finiteBernoulliCovariance E p Y Y := by
  let Xc : Finset ι → ℝ := fun s ↦ X s - finiteBernoulliExpectation E p X
  let Yc : Finset ι → ℝ := fun s ↦ Y s - finiteBernoulliExpectation E p Y
  have hcs :=
    finiteBernoulliExpectation_mul_sq_le_sq_mul_sq (E := E) (p := p) hp0 hp1 Xc Yc
  have hcov :
      finiteBernoulliCovariance E p X Y =
        finiteBernoulliExpectation E p (fun s ↦ Xc s * Yc s) := by
    simpa [Xc, Yc] using finiteBernoulliCovariance_eq_centered E p X Y
  have hvarX :
      finiteBernoulliCovariance E p X X =
        finiteBernoulliExpectation E p (fun s ↦ Xc s ^ 2) := by
    simpa [Xc] using finiteBernoulliCovariance_self_eq_centered_sq E p X
  have hvarY :
      finiteBernoulliCovariance E p Y Y =
        finiteBernoulliExpectation E p (fun s ↦ Yc s ^ 2) := by
    simpa [Yc] using finiteBernoulliCovariance_self_eq_centered_sq E p Y
  simpa [hcov, hvarX, hvarY] using hcs

/-- For an increasing finite trace, `N - 1_A` is increasing. This is the monotonicity input
behind Grimmett's S-shape/reliability lower bound. -/
theorem IsIncreasingTrace.finiteOpenCount_sub_indicator_isIncreasingFinsetFunction
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace E T) :
    IsIncreasingFinsetFunction E
      (fun s ↦ finiteOpenCount s - T.indicator (fun _ ↦ (1 : ℝ)) s) := by
  intro s t hst htE
  change finiteOpenCount s - T.indicator (fun _ ↦ (1 : ℝ)) s ≤
    finiteOpenCount t - T.indicator (fun _ ↦ (1 : ℝ)) t
  by_cases hs : s ∈ T
  · have ht : t ∈ T := hT hst htE hs
    simp [finiteOpenCount, Set.indicator_of_mem hs, Set.indicator_of_mem ht]
    exact Finset.card_le_card hst
  · rw [Set.indicator_of_notMem hs]
    by_cases ht : t ∈ T
    · have hne : s ≠ t := by
        intro hst_eq
        exact hs (by simpa [hst_eq] using ht)
      have hss : s ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩
      have hcardlt : s.card < t.card := Finset.card_lt_card hss
      have hsucc : s.card + 1 ≤ t.card := Nat.succ_le_of_lt hcardlt
      have hsucc_real : (s.card : ℝ) + 1 ≤ (t.card : ℝ) := by
        exact_mod_cast hsucc
      simp [finiteOpenCount, Set.indicator_of_mem ht]
      linarith
    · simp [finiteOpenCount, Set.indicator_of_notMem ht]
      exact Finset.card_le_card hst

/-- Finite monotone reliability covariance lower bound: for increasing `A`,
`cov(N,1_A) ≥ var(1_A) = P(A)(1-P(A))`. This is the numerator form of Grimmett's
inequality (2.37). -/
theorem finiteBernoulliEventProbability_mul_compl_le_covariance_finiteOpenCount
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {p : ℝ} {T : Set (Finset ι)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : IsIncreasingTrace E T) :
    finiteBernoulliEventProbability E p T * (1 - finiteBernoulliEventProbability E p T) ≤
      finiteBernoulliCovariance E p finiteOpenCount
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) := by
  let I : Finset ι → ℝ := fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s
  have hsub_mono :
      IsIncreasingFinsetFunction E (fun s ↦ finiteOpenCount s - I s) := by
    simpa [I] using hT.finiteOpenCount_sub_indicator_isIncreasingFinsetFunction
  have hI_mono : IsIncreasingFinsetFunction E I := by
    simpa [I] using hT.indicator_isIncreasingFinsetFunction
  have hcov_nonneg :
      0 ≤ finiteBernoulliCovariance E p (fun s ↦ finiteOpenCount s - I s) I :=
    finiteBernoulliCovariance_nonneg_of_increasing hp0 hp1 hsub_mono hI_mono
  have hlin := finiteBernoulliCovariance_sub_left E p finiteOpenCount I I
  have hvar := finiteBernoulliCovariance_indicator_self E p T
  rw [hlin] at hcov_nonneg
  change 0 ≤ finiteBernoulliCovariance E p finiteOpenCount I -
      finiteBernoulliCovariance E p I I at hcov_nonneg
  rw [show finiteBernoulliCovariance E p I I =
      finiteBernoulliEventProbability E p T *
        (1 - finiteBernoulliEventProbability E p T) by
    simpa [I] using hvar] at hcov_nonneg
  exact sub_nonneg.mp hcov_nonneg

/-- Divided form of the finite monotone reliability lower bound. Together with
`finiteBernoulliEventProbability_hasDerivAt_covariance_finiteOpenCount`, this is the finite-cube
version of Grimmett's inequality (2.37). -/
theorem finiteBernoulliEventProbability_mul_compl_div_le_covariance_div_finiteOpenCount
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {p : ℝ} {T : Set (Finset ι)}
    (hp0 : 0 < p) (hp1 : p < 1) (hT : IsIncreasingTrace E T) :
    finiteBernoulliEventProbability E p T * (1 - finiteBernoulliEventProbability E p T) /
        (p * (1 - p)) ≤
      finiteBernoulliCovariance E p finiteOpenCount
          (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) /
        (p * (1 - p)) := by
  have hnum :=
    finiteBernoulliEventProbability_mul_compl_le_covariance_finiteOpenCount
      (E := E) (p := p) (T := T) hp0.le hp1.le hT
  have hden : 0 ≤ p * (1 - p) := by
    exact (mul_pos hp0 (sub_pos.mpr hp1)).le
  exact div_le_div_of_nonneg_right hnum hden

/-- Split the expectation of `finiteOpenCount * X` after inserting a fresh coordinate. -/
theorem finiteBernoulliExpectation_finiteOpenCount_mul_insert_split {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ)
    (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p (fun s ↦ finiteOpenCount s * X s) =
      (1 - p) * finiteBernoulliExpectation E p (fun s ↦ finiteOpenCount s * X s) +
        p * finiteBernoulliExpectation E p
          (fun s ↦ (finiteOpenCount s + 1) * X (insert a s)) := by
  rw [finiteBernoulliExpectation_insert_split ha]
  have hopen :
      finiteBernoulliExpectation E p
          (fun s ↦ finiteOpenCount (insert a s) * X (insert a s)) =
        finiteBernoulliExpectation E p
          (fun s ↦ (finiteOpenCount s + 1) * X (insert a s)) := by
    apply finiteBernoulliExpectation_congr
    intro s hsE
    rw [finiteOpenCount_insert_of_notMem (Finset.notMem_mono hsE ha)]
  rw [hopen]

/-- Conditioning decomposition for the covariance with the number of open coordinates. -/
theorem finiteBernoulliCovariance_finiteOpenCount_insert {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliCovariance (insert a E) p finiteOpenCount X =
      (1 - p) * finiteBernoulliCovariance E p finiteOpenCount X +
        p * finiteBernoulliCovariance E p finiteOpenCount (fun s ↦ X (insert a s)) +
          p * (1 - p) *
            (finiteBernoulliExpectation E p (fun s ↦ X (insert a s)) -
              finiteBernoulliExpectation E p X) := by
  rw [finiteBernoulliCovariance, finiteBernoulliCovariance, finiteBernoulliCovariance]
  rw [finiteBernoulliExpectation_finiteOpenCount_mul_insert_split ha]
  rw [finiteBernoulliExpectation_insert_split ha]
  rw [finiteBernoulliExpectation_finiteOpenCount]
  have hopen_count :
      finiteBernoulliExpectation E p (fun s ↦ finiteOpenCount (insert a s)) =
        p * E.card + 1 := by
    have h :
        finiteBernoulliExpectation E p (fun s ↦ finiteOpenCount (insert a s)) =
          finiteBernoulliExpectation E p (fun s ↦ finiteOpenCount s + 1) := by
      apply finiteBernoulliExpectation_congr
      intro s hsE
      exact finiteOpenCount_insert_of_notMem (Finset.notMem_mono hsE ha)
    rw [h, finiteBernoulliExpectation_add, finiteBernoulliExpectation_finiteOpenCount,
      finiteBernoulliExpectation_const]
  rw [hopen_count]
  have hopen_mul :
      finiteBernoulliExpectation E p
          (fun s ↦ (finiteOpenCount s + 1) * X (insert a s)) =
        finiteBernoulliExpectation E p (fun s ↦ finiteOpenCount s * X (insert a s)) +
          finiteBernoulliExpectation E p (fun s ↦ X (insert a s)) := by
    rw [← finiteBernoulliExpectation_add]
    apply finiteBernoulliExpectation_congr
    intro s _hsE
    ring
  rw [hopen_mul]
  rw [finiteBernoulliExpectation_insert_split ha]
  ring

/-- Grimmett's reliability covariance identity on a finite cube, for arbitrary observables:
covariance with the number of open coordinates is `p(1-p)` times the sum of finite
coordinate increments. -/
theorem finiteBernoulliCovariance_finiteOpenCount_eq_mul_derivativeSum {ι : Type*}
    [DecidableEq ι] (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliCovariance E p finiteOpenCount X =
      p * (1 - p) *
        (E.sum fun e ↦ finiteBernoulliExpectation E p (finiteDifference e X)) := by
  induction E using Finset.induction generalizing X with
  | empty =>
      simp [finiteBernoulliCovariance, finiteBernoulliExpectation, finiteOpenCount]
  | insert a E ha ih =>
      let Xopen : Finset ι → ℝ := fun s ↦ X (insert a s)
      rw [finiteBernoulliCovariance_finiteOpenCount_insert ha]
      rw [ih X, ih Xopen]
      rw [Finset.sum_insert ha]
      have hfresh := finiteBernoulliExpectation_finiteDifference_fresh ha p X
      have hold : ∀ e ∈ E,
          finiteBernoulliExpectation (insert a E) p (finiteDifference e X) =
            (1 - p) * finiteBernoulliExpectation E p (finiteDifference e X) +
              p * finiteBernoulliExpectation E p (finiteDifference e Xopen) := by
        intro e he
        simpa [Xopen] using finiteBernoulliExpectation_finiteDifference_old_insert_split ha he p X
      rw [hfresh]
      rw [show E.sum (fun e ↦ finiteBernoulliExpectation (insert a E) p
              (finiteDifference e X)) =
            E.sum (fun e ↦
              (1 - p) * finiteBernoulliExpectation E p (finiteDifference e X) +
                p * finiteBernoulliExpectation E p (finiteDifference e Xopen)) by
        apply Finset.sum_congr rfl
        intro e he
        exact hold e he]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp [Xopen]
      ring

/-- Variance of the number of open coordinates in a finite Bernoulli cube. -/
theorem finiteBernoulliCovariance_finiteOpenCount_self {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (p : ℝ) :
    finiteBernoulliCovariance E p finiteOpenCount finiteOpenCount =
      p * (1 - p) * E.card := by
  rw [finiteBernoulliCovariance_finiteOpenCount_eq_mul_derivativeSum]
  rw [show E.sum (fun e ↦
        finiteBernoulliExpectation E p (finiteDifference e finiteOpenCount)) =
      E.sum (fun _ ↦ (1 : ℝ)) by
    apply Finset.sum_congr rfl
    intro e _he
    exact finiteBernoulliExpectation_finiteDifference_finiteOpenCount E p e]
  simp

/-- Finite Cauchy-Schwarz upper reliability bound, the numerator form of Grimmett's
inequality (2.36)(a). -/
theorem finiteBernoulliCovariance_finiteOpenCount_indicator_sq_le
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Set (Finset ι)) :
    (finiteBernoulliCovariance E p finiteOpenCount
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s)) ^ 2 ≤
      (p * (1 - p) * E.card) *
        (finiteBernoulliEventProbability E p T *
          (1 - finiteBernoulliEventProbability E p T)) := by
  let I : Finset ι → ℝ := fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s
  have hcs :=
    finiteBernoulliCovariance_sq_le_mul_self (E := E) (p := p)
      (X := finiteOpenCount) (Y := I) hp0 hp1
  have hN := finiteBernoulliCovariance_finiteOpenCount_self E p
  have hI := finiteBernoulliCovariance_indicator_self E p T
  simpa [I, hN, hI] using hcs

/-- Finite Cauchy-Schwarz upper reliability bound in the divided form used with
Theorem (2.34). This is the square of Grimmett's inequality (2.36)(a), with the
finite derivative written as the covariance quotient. -/
theorem finiteBernoulliEventProbability_covariance_div_sq_le
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (T : Set (Finset ι)) :
    (finiteBernoulliCovariance E p finiteOpenCount
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) / (p * (1 - p))) ^ 2 ≤
      (E.card : ℝ) *
        (finiteBernoulliEventProbability E p T *
          (1 - finiteBernoulliEventProbability E p T)) / (p * (1 - p)) := by
  let c : ℝ :=
    finiteBernoulliCovariance E p finiteOpenCount
      (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s)
  let v : ℝ :=
    finiteBernoulliEventProbability E p T *
      (1 - finiteBernoulliEventProbability E p T)
  let d : ℝ := p * (1 - p)
  have hnum :
      c ^ 2 ≤ (d * E.card) * v := by
    simpa [c, v, d, mul_assoc] using
      finiteBernoulliCovariance_finiteOpenCount_indicator_sq_le
        (E := E) (p := p) hp0.le hp1.le T
  have hdpos : 0 < d := by
    exact mul_pos hp0 (sub_pos.mpr hp1)
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdiv : c ^ 2 / d ^ 2 ≤ ((d * E.card) * v) / d ^ 2 :=
    div_le_div_of_nonneg_right hnum (sq_nonneg d)
  calc
    (c / d) ^ 2 = c ^ 2 / d ^ 2 := by
      field_simp [hdne]
    _ ≤ ((d * E.card) * v) / d ^ 2 := hdiv
    _ = (E.card : ℝ) * v / d := by
      field_simp [hdne]

/-- Finite Cauchy-Schwarz upper reliability bound in the square-root form of
Grimmett's inequality (2.36)(a), with the finite derivative written as the covariance quotient. -/
theorem finiteBernoulliEventProbability_abs_covariance_div_le_sqrt
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (T : Set (Finset ι)) :
    |finiteBernoulliCovariance E p finiteOpenCount
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) / (p * (1 - p))| ≤
      √((E.card : ℝ) *
        (finiteBernoulliEventProbability E p T *
          (1 - finiteBernoulliEventProbability E p T)) / (p * (1 - p))) := by
  exact Real.abs_le_sqrt
    (finiteBernoulliEventProbability_covariance_div_sq_le (E := E) (p := p) hp0 hp1 T)

/-- The derivative of a finite-cube expectation written in Grimmett's reliability covariance
form. This is the random-variable version of Theorem (2.34). -/
theorem finiteBernoulliExpectation_hasDerivAt_covariance_finiteOpenCount {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (X : Finset ι → ℝ) :
    HasDerivAt (fun x : ℝ ↦ finiteBernoulliExpectation E x X)
      (finiteBernoulliCovariance E p finiteOpenCount X / (p * (1 - p))) p := by
  have hderiv := finiteBernoulliExpectation_hasDerivAt (E := E) (p := p) X
  apply hderiv.congr_deriv
  have hcov := finiteBernoulliCovariance_finiteOpenCount_eq_mul_derivativeSum E p X
  have hden : p * (1 - p) ≠ 0 := by
    refine mul_ne_zero hp0 ?_
    intro h
    exact hp1 (by linarith)
  rw [hcov]
  symm
  exact mul_div_cancel_left₀ _ hden

/-- Grimmett's Theorem (2.34), finite-event form.  The derivative of a finite event probability
is covariance with the finite open-coordinate count divided by `p(1-p)`. -/
theorem finiteBernoulliEventProbability_hasDerivAt_covariance_finiteOpenCount {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (T : Set (Finset ι)) :
    HasDerivAt (fun x : ℝ ↦ finiteBernoulliEventProbability E x T)
      (finiteBernoulliCovariance E p finiteOpenCount
        (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s) / (p * (1 - p))) p := by
  simpa [finiteBernoulliEventProbability] using
    finiteBernoulliExpectation_hasDerivAt_covariance_finiteOpenCount
      (E := E) (p := p) hp0 hp1 (fun s ↦ T.indicator (fun _ ↦ (1 : ℝ)) s)

end Percolation
