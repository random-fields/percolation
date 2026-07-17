import Percolation.Critical.SupercriticalFiniteClusterTail
import Percolation.Critical.ClusterAnalyticity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Smooth supercritical animal series

This file develops the analytic part of Grimmett's Theorem 8.92.  The probabilistic input is a
uniform stretched-exponential bound for the finite-cluster size distribution on a compact
parameter interval.  All higher derivatives of a size-`n` animal level cost only a polynomial
in `n`, so the level series and all its derivatives converge locally uniformly.
-/

namespace Percolation

open Set Filter
open scoped BigOperators ENNReal unitInterval Topology

noncomputable section

set_option maxHeartbeats 800000

/-- Real weight of one concrete rooted bond animal. -/
def realAnimalWeight {d n : ℕ} (A : CubicBondAnimal d n) (p : ℝ) : ℝ :=
  p ^ A.edges.card * (1 - p) ^ A.boundary.card

/-- The polynomial whose value on the physical interval is
`Pₚ(|C| = n)`. -/
def finiteClusterProbabilityPolynomialLevel (d n : ℕ) (p : ℝ) : ℝ :=
  ∑ A : CubicBondAnimal d n, realAnimalWeight A p

theorem finiteClusterProbabilityPolynomialLevel_eq_probability
    (d n : ℕ) (p : I) :
    finiteClusterProbabilityPolynomialLevel d n p =
      finiteClusterSizeProbability d p n := by
  rw [finiteClusterSizeProbability_eq_sum_animals]
  rfl

theorem realAnimalWeight_contDiff {d n : ℕ} (A : CubicBondAnimal d n) :
    ContDiff ℝ ⊤ (realAnimalWeight A) := by
  unfold realAnimalWeight
  fun_prop

theorem finiteClusterProbabilityPolynomialLevel_contDiff (d n : ℕ) :
    ContDiff ℝ ⊤ (finiteClusterProbabilityPolynomialLevel d n) := by
  unfold finiteClusterProbabilityPolynomialLevel
  exact ContDiff.sum fun A _hA ↦ realAnimalWeight_contDiff A

theorem iteratedDeriv_one_sub_pow (b k : ℕ) (p : ℝ) :
    iteratedDeriv k (fun x : ℝ ↦ (1 - x) ^ b) p =
      (-1 : ℝ) ^ k * b.descFactorial k * (1 - p) ^ (b - k) := by
  have h := congrFun
    (iteratedDeriv_comp_const_sub k (fun x : ℝ ↦ x ^ b) 1) p
  simp only [iteratedDeriv_pow, smul_eq_mul] at h
  convert h using 1
  · ring

/-- Removing at most `k` powers costs at most `a⁻ᵏ` on `[a,1]`. -/
theorem pow_sub_le_inv_pow_mul_pow
    {a p : ℝ} {m i k : ℕ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hap : a ≤ p)
    (hi : i ≤ m) (hik : i ≤ k) :
    p ^ (m - i) ≤ a⁻¹ ^ k * p ^ m := by
  have hp0 : 0 < p := ha0.trans_le hap
  have hak0 : 0 < a ^ k := pow_pos ha0 k
  have hpi0 : 0 < p ^ i := pow_pos hp0 i
  have haki : a ^ k ≤ a ^ i := pow_le_pow_of_le_one ha0.le ha1 hik
  have haip : a ^ i ≤ p ^ i := pow_le_pow_left₀ ha0.le hap i
  have hinv : (p ^ i)⁻¹ ≤ (a ^ k)⁻¹ :=
    (inv_le_inv₀ hpi0 hak0).2 (haki.trans haip)
  calc
    p ^ (m - i) = p ^ m * (p ^ i)⁻¹ := by
      rw [← div_eq_mul_inv, eq_div_iff (pow_ne_zero i hp0.ne')]
      rw [← pow_add, Nat.sub_add_cancel hi]
    _ ≤ p ^ m * (a ^ k)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg hp0.le m)
    _ = a⁻¹ ^ k * p ^ m := by rw [inv_pow]; ring

/-- Exact Leibniz formula for the `k`-th derivative of a real animal weight. -/
theorem iteratedDeriv_realAnimalWeight
    {d n : ℕ} (A : CubicBondAnimal d n) (k : ℕ) (p : ℝ) :
    iteratedDeriv k (realAnimalWeight A) p =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) *
          ((A.edges.card.descFactorial i : ℕ) : ℝ) * p ^ (A.edges.card - i) *
          ((-1 : ℝ) ^ (k - i) *
            ((A.boundary.card.descFactorial (k - i) : ℕ) : ℝ) *
            (1 - p) ^ (A.boundary.card - (k - i))) := by
  change iteratedDeriv k
    (fun x : ℝ ↦ x ^ A.edges.card * (1 - x) ^ A.boundary.card) p = _
  rw [show (fun x : ℝ ↦ x ^ A.edges.card * (1 - x) ^ A.boundary.card) =
      (fun x : ℝ ↦ x ^ A.edges.card) *
        (fun x : ℝ ↦ (1 - x) ^ A.boundary.card) by rfl]
  rw [iteratedDeriv_mul
    (by fun_prop : ContDiffAt ℝ k (fun x : ℝ ↦ x ^ A.edges.card) p)
    (by fun_prop : ContDiffAt ℝ k (fun x : ℝ ↦ (1 - x) ^ A.boundary.card) p)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [iteratedDeriv_pow, iteratedDeriv_one_sub_pow]
  ring

/-- A dimension/size bound simultaneously dominating the occupied- and boundary-edge counts of
a rooted size-`n` animal.  The added one makes it usable at every endpoint. -/
def animalDerivativeDegreeBound (d n : ℕ) : ℝ :=
  2 * d * n + 1

theorem edges_card_cast_le_animalDerivativeDegreeBound
    {d n : ℕ} (A : CubicBondAnimal d n) :
    (A.edges.card : ℝ) ≤ animalDerivativeDegreeBound d n := by
  unfold animalDerivativeDegreeBound
  exact_mod_cast A.edges_card_upper.trans
    (by nlinarith [Nat.zero_le (d * n)] : d * n ≤ 2 * d * n + 1)

theorem boundary_card_cast_le_animalDerivativeDegreeBound
    {d n : ℕ} (A : CubicBondAnimal d n) :
    (A.boundary.card : ℝ) ≤ animalDerivativeDegreeBound d n := by
  unfold animalDerivativeDegreeBound
  exact_mod_cast A.boundary_card_le.trans (by omega : 2 * d * n ≤ 2 * d * n + 1)

theorem animalDerivativeDegreeBound_one_le (d n : ℕ) :
    (1 : ℝ) ≤ animalDerivativeDegreeBound d n := by
  unfold animalDerivativeDegreeBound
  norm_num
  positivity

/-- Uniform `k`-th derivative cost of one animal on a compact subinterval of `(0,1)`.
The intentionally loose polynomial constant keeps the proof independent of cancellation. -/
theorem norm_iteratedDeriv_realAnimalWeight_le
    {d n : ℕ} (A : CubicBondAnimal d n) (k : ℕ)
    {a b p : ℝ} (ha0 : 0 < a) (hap : a ≤ p) (hpb : p ≤ b) (hb1 : b < 1) :
    ‖iteratedDeriv k (realAnimalWeight A) p‖ ≤
      (k + 1 : ℕ) * (2 : ℝ) ^ k * animalDerivativeDegreeBound d n ^ k *
        a⁻¹ ^ k * (1 - b)⁻¹ ^ k * realAnimalWeight A p := by
  let B : ℝ := animalDerivativeDegreeBound d n
  let q : ℝ := 1 - p
  let q₀ : ℝ := 1 - b
  let M : ℝ := (2 : ℝ) ^ k * B ^ k * a⁻¹ ^ k * q₀⁻¹ ^ k *
    realAnimalWeight A p
  have ha1 : a ≤ 1 := hap.trans hpb |>.trans hb1.le
  have hp0 : 0 ≤ p := ha0.le.trans hap
  have hp1 : p ≤ 1 := hpb.trans hb1.le
  have hq₀0 : 0 < q₀ := sub_pos.mpr hb1
  have hq₀1 : q₀ ≤ 1 := by dsimp [q₀]; linarith
  have hq₀q : q₀ ≤ q := by dsimp [q₀, q]; linarith
  have hB0 : 0 ≤ B := (animalDerivativeDegreeBound_one_le d n).trans' zero_le_one
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hB0 _))
          (pow_nonneg (inv_nonneg.mpr ha0.le) _))
        (pow_nonneg (inv_nonneg.mpr hq₀0.le) _))
      (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _))
  rw [iteratedDeriv_realAnimalWeight]
  calc
    ‖∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) *
            (A.edges.card.descFactorial i : ℝ) * p ^ (A.edges.card - i) *
            ((-1 : ℝ) ^ (k - i) *
              (A.boundary.card.descFactorial (k - i) : ℝ) *
              (1 - p) ^ (A.boundary.card - (k - i)))‖ ≤
        ∑ i ∈ Finset.range (k + 1),
          ‖(k.choose i : ℝ) *
            (A.edges.card.descFactorial i : ℝ) * p ^ (A.edges.card - i) *
            ((-1 : ℝ) ^ (k - i) *
              (A.boundary.card.descFactorial (k - i) : ℝ) *
              (1 - p) ^ (A.boundary.card - (k - i)))‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (k + 1), M := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      by_cases him : i ≤ A.edges.card
      · by_cases hkb : k - i ≤ A.boundary.card
        · have hchoose : (k.choose i : ℝ) ≤ (2 : ℝ) ^ k := by
            exact_mod_cast Nat.choose_le_two_pow k i
          have hmfac : (A.edges.card.descFactorial i : ℝ) ≤ B ^ i := by
            calc
              (A.edges.card.descFactorial i : ℝ) ≤ (A.edges.card : ℝ) ^ i := by
                exact_mod_cast A.edges.card.descFactorial_le_pow i
              _ ≤ B ^ i := by
                gcongr
                exact edges_card_cast_le_animalDerivativeDegreeBound A
          have hbfac : (A.boundary.card.descFactorial (k - i) : ℝ) ≤
              B ^ (k - i) := by
            calc
              (A.boundary.card.descFactorial (k - i) : ℝ) ≤
                  (A.boundary.card : ℝ) ^ (k - i) := by
                exact_mod_cast A.boundary.card.descFactorial_le_pow (k - i)
              _ ≤ B ^ (k - i) := by
                gcongr
                exact boundary_card_cast_le_animalDerivativeDegreeBound A
          have hpSub : p ^ (A.edges.card - i) ≤
              a⁻¹ ^ k * p ^ A.edges.card :=
            pow_sub_le_inv_pow_mul_pow ha0 ha1 hap him hik
          have hqSub : q ^ (A.boundary.card - (k - i)) ≤
              q₀⁻¹ ^ k * q ^ A.boundary.card :=
            pow_sub_le_inv_pow_mul_pow hq₀0 hq₀1 hq₀q hkb (Nat.sub_le k i)
          have hchoose0 : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          have hmfac0 : 0 ≤ (A.edges.card.descFactorial i : ℝ) := Nat.cast_nonneg _
          have hbfac0 : 0 ≤ (A.boundary.card.descFactorial (k - i) : ℝ) :=
            Nat.cast_nonneg _
          rw [Real.norm_eq_abs]
          simp only [abs_mul, abs_pow, abs_neg, abs_one,
            one_pow, one_mul, abs_of_nonneg hp0, abs_of_nonneg (sub_nonneg.mpr hp1)]
          rw [abs_of_nonneg hchoose0, abs_of_nonneg hmfac0, abs_of_nonneg hbfac0]
          dsimp only [q] at hqSub
          calc
            (k.choose i : ℝ) * (A.edges.card.descFactorial i : ℝ) *
                p ^ (A.edges.card - i) *
                ((A.boundary.card.descFactorial (k - i) : ℝ) *
                  (1 - p) ^ (A.boundary.card - (k - i))) ≤
                (2 : ℝ) ^ k * B ^ i * (a⁻¹ ^ k * p ^ A.edges.card) *
                  (B ^ (k - i) *
                    (q₀⁻¹ ^ k * (1 - p) ^ A.boundary.card)) := by
              gcongr
            _ = M := by
              have hBpow : B ^ i * B ^ (k - i) = B ^ k := by
                rw [← pow_add, Nat.add_sub_of_le hik]
              dsimp [M, realAnimalWeight]
              calc
                (2 : ℝ) ^ k * B ^ i * (a⁻¹ ^ k * p ^ A.edges.card) *
                    (B ^ (k - i) *
                      (q₀⁻¹ ^ k * (1 - p) ^ A.boundary.card)) =
                    (B ^ i * B ^ (k - i)) *
                      ((2 : ℝ) ^ k * a⁻¹ ^ k * q₀⁻¹ ^ k *
                        (p ^ A.edges.card * (1 - p) ^ A.boundary.card)) := by ring
                _ = _ := by rw [hBpow]; ring
        · have hz : A.boundary.card.descFactorial (k - i) = 0 :=
            Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hkb)
          simp [hz, hM0]
      · have hz : A.edges.card.descFactorial i = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge him)
        simp [hz, hM0]
    _ = (k + 1 : ℕ) * M := by simp
    _ = (k + 1 : ℕ) * (2 : ℝ) ^ k * animalDerivativeDegreeBound d n ^ k *
          a⁻¹ ^ k * (1 - b)⁻¹ ^ k * realAnimalWeight A p := by
      dsimp [M, B, q₀]
      push_cast
      ring

/-- Summing the animal-by-animal estimate gives a derivative bound for the entire exact-size
level.  Crucially, the right side is the physical level probability, not the number of animals. -/
theorem norm_iteratedDeriv_finiteClusterProbabilityPolynomialLevel_le
    {d n k : ℕ} {a b p : ℝ}
    (ha0 : 0 < a) (hap : a ≤ p) (hpb : p ≤ b) (hb1 : b < 1) :
    ‖iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) p‖ ≤
      (k + 1 : ℕ) * (2 : ℝ) ^ k * animalDerivativeDegreeBound d n ^ k *
        a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
          finiteClusterProbabilityPolynomialLevel d n p := by
  rw [show iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) p =
      ∑ A : CubicBondAnimal d n, iteratedDeriv k (realAnimalWeight A) p by
    unfold finiteClusterProbabilityPolynomialLevel
    exact iteratedDeriv_fun_sum fun A _hA ↦
      (realAnimalWeight_contDiff A).contDiffAt.of_le le_top]
  calc
    ‖∑ A : CubicBondAnimal d n, iteratedDeriv k (realAnimalWeight A) p‖ ≤
        ∑ A : CubicBondAnimal d n, ‖iteratedDeriv k (realAnimalWeight A) p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ A : CubicBondAnimal d n,
        ((k + 1 : ℕ) * (2 : ℝ) ^ k * animalDerivativeDegreeBound d n ^ k *
          a⁻¹ ^ k * (1 - b)⁻¹ ^ k) * realAnimalWeight A p := by
      apply Finset.sum_le_sum
      intro A _hA
      simpa only [mul_assoc] using
        norm_iteratedDeriv_realAnimalWeight_le A k ha0 hap hpb hb1
    _ = (k + 1 : ℕ) * (2 : ℝ) ^ k * animalDerivativeDegreeBound d n ^ k *
        a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
          finiteClusterProbabilityPolynomialLevel d n p := by
      unfold finiteClusterProbabilityPolynomialLevel
      rw [Finset.mul_sum]

/-- Every polynomial multiple of a stretched exponential is summable.  This is the analytic
fact that allows arbitrary-order differentiation in Theorem 8.92. -/
theorem summable_nat_pow_mul_exp_neg_mul_rpow
    {alpha eta : ℝ} (halpha : 0 < alpha) (heta : 0 < eta) (k : ℕ) :
    Summable fun n : ℕ ↦
      (n : ℝ) ^ k * Real.exp (-eta * (n : ℝ) ^ alpha) := by
  have hlo : (fun x : ℝ ↦ Real.log x) =o[atTop]
      (fun x : ℝ ↦ x ^ alpha) :=
    isLittleO_log_rpow_atTop halpha
  have hloNat := hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have hk2pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hbound := hloNat.bound (div_pos heta hk2pos)
  have hevent : ∀ᶠ n : ℕ in atTop,
      ‖(n : ℝ) ^ k * Real.exp (-eta * (n : ℝ) ^ alpha)‖ ≤
        (n : ℝ) ^ (-2 : ℝ) := by
    filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with n hnlog hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hrpow0 : 0 ≤ (n : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg n) alpha
    have hnlog' : Real.log (n : ℝ) ≤
        eta / ((k : ℝ) + 2) * (n : ℝ) ^ alpha := by
      dsimp [Function.comp_def] at hnlog
      rw [abs_of_nonneg hlog0, abs_of_nonneg hrpow0] at hnlog
      exact hnlog
    have hlog : ((k : ℝ) + 2) * Real.log (n : ℝ) ≤
        eta * (n : ℝ) ^ alpha := by
      calc
        ((k : ℝ) + 2) * Real.log (n : ℝ) ≤
            ((k : ℝ) + 2) *
              (eta / ((k : ℝ) + 2) * (n : ℝ) ^ alpha) :=
          mul_le_mul_of_nonneg_left hnlog' hk2pos.le
        _ = eta * (n : ℝ) ^ alpha := by field_simp
    have hexp : (n : ℝ) ^ k * Real.exp (-eta * (n : ℝ) ^ alpha) ≤
        (n : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos,
        Real.rpow_def_of_pos hnpos]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Real.rpow_def_of_pos hnpos] at hlog
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos
      (mul_pos (pow_pos hnpos k) (Real.exp_pos _))]
    exact hexp
  exact (Real.summable_nat_rpow.mpr (by norm_num)).of_norm_bounded_eventually_nat hevent

theorem summable_nat_succ_pow_mul_exp_neg_mul_rpow
    {alpha eta : ℝ} (halpha : 0 < alpha) (heta : 0 < eta) (k : ℕ) :
    Summable fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) ^ k * Real.exp (-eta * (n : ℝ) ^ alpha) := by
  have hs := (summable_nat_pow_mul_exp_neg_mul_rpow halpha heta k).mul_left ((2 : ℝ) ^ k)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsucc : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact_mod_cast (by omega : n + 1 ≤ 2 * n)
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (Real.exp_pos _).le)]
  calc
    ((n + 1 : ℕ) : ℝ) ^ k * Real.exp (-eta * (n : ℝ) ^ alpha) ≤
        (2 * (n : ℝ)) ^ k * Real.exp (-eta * (n : ℝ) ^ alpha) := by
      gcongr
    _ = (2 : ℝ) ^ k *
        ((n : ℝ) ^ k * Real.exp (-eta * (n : ℝ) ^ alpha)) := by
      rw [mul_pow]
      ring

/-- Compact-uniform exact-size tail hypothesis used by the analytic part of Theorem 8.92. -/
def UniformFiniteClusterSizeProbabilityStretchedExponential
    (d : ℕ) (a b eta : ℝ) : Prop :=
  ∀ p : I, a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b → ∀ n : ℕ,
    finiteClusterSizeProbability d p n ≤
      Real.exp (-eta * (n : ℝ) ^ ((d : ℝ)⁻¹))

/-- Compact-uniform version of Grimmett's bound (8.91). -/
def UniformFiniteClusterSizeTailStretchedExponential
    (d : ℕ) (a b eta : ℝ) : Prop :=
  ∀ p : I, a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b → ∀ n : ℕ,
    finiteClusterSizeTail d p n ≤
      Real.exp (-eta * (n : ℝ) ^ ((d : ℝ)⁻¹))

theorem uniformFiniteClusterSizeProbability_of_tail
    {d : ℕ} {a b eta : ℝ}
    (hTail : UniformFiniteClusterSizeTailStretchedExponential d a b eta) :
    UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta := by
  intro p hp n
  exact (finiteClusterSizeProbability_le_finiteClusterSizeTail d p n).trans
    (hTail p hp n)

def finiteClusterProbabilityDerivativeSeries (d k : ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) p

theorem animalDerivativeDegreeBound_le_mul_succ (d n : ℕ) :
    animalDerivativeDegreeBound d n ≤ (2 * d + 1 : ℕ) * (n + 1) := by
  unfold animalDerivativeDegreeBound
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

def finiteClusterDerivativeMajorant
    (d k : ℕ) (a b eta : ℝ) (n : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k * ((2 * d + 1 : ℕ) : ℝ) ^ k *
    a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
      (((n + 1 : ℕ) : ℝ) ^ k *
        Real.exp (-eta * (n : ℝ) ^ ((d : ℝ)⁻¹)))

theorem summable_finiteClusterDerivativeMajorant
    {d : ℕ} (hd : 0 < d) {a b eta : ℝ} (heta : 0 < eta) (k : ℕ) :
    Summable (finiteClusterDerivativeMajorant d k a b eta) := by
  unfold finiteClusterDerivativeMajorant
  apply Summable.mul_left
  exact summable_nat_succ_pow_mul_exp_neg_mul_rpow
    (inv_pos.mpr (by exact_mod_cast hd : (0 : ℝ) < d)) heta k

theorem norm_iteratedDeriv_finiteClusterProbabilityPolynomialLevel_le_majorant
    {d : ℕ} {a b eta : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta)
    (k n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo a b) :
    ‖iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) p‖ ≤
      finiteClusterDerivativeMajorant d k a b eta n := by
  let pI : I := ⟨p, (ha0.trans hp.1).le, (hp.2.trans hb1).le⟩
  have hprob := hTail pI ⟨hp.1.le, hp.2.le⟩ n
  have hlevel : finiteClusterProbabilityPolynomialLevel d n p =
      finiteClusterSizeProbability d pI n := by
    simpa [pI] using finiteClusterProbabilityPolynomialLevel_eq_probability d n pI
  have hdegree0 : 0 ≤ animalDerivativeDegreeBound d n :=
    zero_le_one.trans (animalDerivativeDegreeBound_one_le d n)
  have hfactor0 : 0 ≤
      ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k *
        animalDerivativeDegreeBound d n ^ k * a⁻¹ ^ k * (1 - b)⁻¹ ^ k := by
    positivity
  calc
    ‖iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) p‖ ≤
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k *
          animalDerivativeDegreeBound d n ^ k * a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
            finiteClusterProbabilityPolynomialLevel d n p :=
      norm_iteratedDeriv_finiteClusterProbabilityPolynomialLevel_le
        ha0 hp.1.le hp.2.le hb1
    _ ≤ ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k *
          animalDerivativeDegreeBound d n ^ k * a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
            Real.exp (-eta * (n : ℝ) ^ ((d : ℝ)⁻¹)) := by
      rw [hlevel]
      exact mul_le_mul_of_nonneg_left hprob hfactor0
    _ ≤ finiteClusterDerivativeMajorant d k a b eta n := by
      unfold finiteClusterDerivativeMajorant
      have hdegree := animalDerivativeDegreeBound_le_mul_succ d n
      have hdegree' : animalDerivativeDegreeBound d n ≤
          ((2 * d + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hdegree ⊢
        exact hdegree
      have hpow : animalDerivativeDegreeBound d n ^ k ≤
          (((2 * d + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ k := by
        exact pow_le_pow_left₀ hdegree0 hdegree' k
      rw [mul_pow] at hpow
      have hexp0 : 0 ≤ Real.exp (-eta * (n : ℝ) ^ ((d : ℝ)⁻¹)) :=
        (Real.exp_pos _).le
      have haInv0 : 0 ≤ a⁻¹ ^ k := pow_nonneg (inv_nonneg.mpr ha0.le) k
      have hbInv0 : 0 ≤ (1 - b)⁻¹ ^ k :=
        pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hb1).le) k
      calc
        ((k + 1 : ℕ) : ℝ) * 2 ^ k * animalDerivativeDegreeBound d n ^ k *
              a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
              Real.exp (-eta * (n : ℝ) ^ (d : ℝ)⁻¹) ≤
            ((k + 1 : ℕ) : ℝ) * 2 ^ k *
              ((((2 * d + 1 : ℕ) : ℝ) ^ k * ((n + 1 : ℕ) : ℝ) ^ k)) *
              a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
              Real.exp (-eta * (n : ℝ) ^ (d : ℝ)⁻¹) := by
          gcongr
        _ = ((k + 1 : ℕ) : ℝ) * 2 ^ k * ((2 * d + 1 : ℕ) : ℝ) ^ k *
              a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
              (((n + 1 : ℕ) : ℝ) ^ k *
                Real.exp (-eta * (n : ℝ) ^ (d : ℝ)⁻¹)) := by ring

theorem finiteClusterProbabilityDerivativeSeries_hasDerivAt
    {d : ℕ} (hd : 0 < d) {a b eta : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta)
    (k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo a b) :
    HasDerivAt (finiteClusterProbabilityDerivativeSeries d k)
      (finiteClusterProbabilityDerivativeSeries d (k + 1) p) p := by
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by dsimp [c]; constructor <;> linarith
  have hterm : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo a b →
      HasDerivAt
        (iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n))
        (iteratedDeriv (k + 1) (finiteClusterProbabilityPolynomialLevel d n) y) y := by
    intro n y _hy
    have hdiff : Differentiable ℝ
        (iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n)) :=
      (finiteClusterProbabilityPolynomialLevel_contDiff d n).differentiable_iteratedDeriv
        k (by simp)
    have hhas := (hdiff y).hasDerivAt
    simpa only [iteratedDeriv_succ] using hhas
  have hbase : Summable fun n : ℕ ↦
      iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) c := by
    exact (summable_finiteClusterDerivativeMajorant hd heta k).of_norm_bounded
      (fun n ↦
        norm_iteratedDeriv_finiteClusterProbabilityPolynomialLevel_le_majorant
          ha0 hb1 hTail k n hc)
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (summable_finiteClusterDerivativeMajorant hd heta (k + 1))
    isOpen_Ioo isPreconnected_Ioo hterm
    (fun n y hy ↦
      norm_iteratedDeriv_finiteClusterProbabilityPolynomialLevel_le_majorant
        ha0 hb1 hTail (k + 1) n hy)
    hc hbase hp
  simpa only [finiteClusterProbabilityDerivativeSeries] using hsum

/-- The exact-size animal series is smooth on a compact interval whenever its probabilities have
a compact-uniform stretched-exponential bound there. -/
theorem finiteClusterProbabilityDerivativeSeries_contDiffOn
    {d : ℕ} (hd : 0 < d) {a b eta : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta)
    (k m : ℕ) :
    ContDiffOn ℝ m (finiteClusterProbabilityDerivativeSeries d k) (Set.Ioo a b) := by
  induction m generalizing k with
  | zero =>
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (finiteClusterProbabilityDerivativeSeries d k) (Set.Ioo a b)
      rw [contDiffOn_zero]
      intro p hp
      exact (finiteClusterProbabilityDerivativeSeries_hasDerivAt
        hd ha0 hab hb1 heta hTail k hp).continuousAt.continuousWithinAt
  | succ m ih =>
      change ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
        (finiteClusterProbabilityDerivativeSeries d k) (Set.Ioo a b)
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨?_, by simp, ?_⟩
      · intro p hp
        exact (finiteClusterProbabilityDerivativeSeries_hasDerivAt
          hd ha0 hab hb1 heta hTail k hp).differentiableAt.differentiableWithinAt
      · refine (ih (k + 1)).congr fun p hp ↦ ?_
        exact (finiteClusterProbabilityDerivativeSeries_hasDerivAt
          hd ha0 hab hb1 heta hTail k hp).deriv

theorem finiteClusterProbabilitySeries_contDiffOn_infty
    {d : ℕ} (hd : 0 < d) {a b eta : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (finiteClusterProbabilityDerivativeSeries d 0)
      (Set.Ioo a b) := by
  rw [contDiffOn_infty]
  exact fun m ↦ finiteClusterProbabilityDerivativeSeries_contDiffOn
    hd ha0 hab hb1 heta hTail 0 m

/-- Real animal-series extension of the percolation probability. -/
def thetaAnimalSeries (d : ℕ) (p : ℝ) : ℝ :=
  1 - finiteClusterProbabilityDerivativeSeries d 0 p

theorem finiteClusterProbabilityDerivativeSeries_zero_eq_tsum
    (d : ℕ) (p : ℝ) :
    finiteClusterProbabilityDerivativeSeries d 0 p =
      ∑' n : ℕ, finiteClusterProbabilityPolynomialLevel d n p := by
  unfold finiteClusterProbabilityDerivativeSeries
  apply tsum_congr
  intro n
  simp

theorem thetaAnimalSeries_eq_theta
    (d : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    thetaAnimalSeries d p = theta d ⟨p, hp0, hp1⟩ := by
  let pI : I := ⟨p, hp0, hp1⟩
  unfold thetaAnimalSeries
  rw [finiteClusterProbabilityDerivativeSeries_zero_eq_tsum]
  calc
    1 - ∑' n : ℕ, finiteClusterProbabilityPolynomialLevel d n p =
        1 - ∑' n : ℕ, finiteClusterSizeProbability d pI n := by
      congr 1
      apply tsum_congr
      intro n
      simpa [pI] using finiteClusterProbabilityPolynomialLevel_eq_probability d n pI
    _ = theta d pI := by
      rw [tsum_finiteClusterSizeProbability_eq_one_sub_theta]
      ring

/-- Analytic core of Grimmett's Theorem 8.92 for the percolation probability.  The separate
probabilistic part of the chapter supplies `hTail` uniformly on compact supercritical intervals. -/
theorem thetaAnimalSeries_contDiffOn_infty_of_uniform_stretchedExponential
    {d : ℕ} (hd : 0 < d) {a b eta : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (thetaAnimalSeries d) (Set.Ioo a b) := by
  exact contDiffOn_const.sub
    (finiteClusterProbabilitySeries_contDiffOn_infty
      hd ha0 hab hb1 heta hTail)

/-! ### Polynomially weighted animal series -/

def weightedFiniteClusterProbabilityDerivativeSeries
    (d : ℕ) (w : ℕ → ℝ) (k : ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, w n * iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) p

def weightedFiniteClusterDerivativeMajorant
    (d : ℕ) (w : ℕ → ℝ) (k : ℕ) (a b eta : ℝ) (n : ℕ) : ℝ :=
  ‖w n‖ * finiteClusterDerivativeMajorant d k a b eta n

theorem summable_weightedFiniteClusterDerivativeMajorant
    {d : ℕ} (hd : 0 < d) {w : ℕ → ℝ} {r : ℕ}
    (hw : ∀ n : ℕ, ‖w n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ r)
    {a b eta : ℝ} (ha0 : 0 < a) (hb1 : b < 1) (heta : 0 < eta) (k : ℕ) :
    Summable (weightedFiniteClusterDerivativeMajorant d w k a b eta) := by
  let C : ℝ := ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ k *
    ((2 * d + 1 : ℕ) : ℝ) ^ k * a⁻¹ ^ k * (1 - b)⁻¹ ^ k
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hs :=
    (summable_nat_succ_pow_mul_exp_neg_mul_rpow
      (inv_pos.mpr (by exact_mod_cast hd : (0 : ℝ) < d)) heta (r + k)).mul_left C
  apply hs.of_norm_bounded
  intro n
  have hmajor0 : 0 ≤ finiteClusterDerivativeMajorant d k a b eta n := by
    unfold finiteClusterDerivativeMajorant
    positivity
  unfold weightedFiniteClusterDerivativeMajorant
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg (w n)) hmajor0)]
  unfold finiteClusterDerivativeMajorant
  calc
    ‖w n‖ *
        (((k + 1 : ℕ) : ℝ) * 2 ^ k * ((2 * d + 1 : ℕ) : ℝ) ^ k *
          a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
          (((n + 1 : ℕ) : ℝ) ^ k *
            Real.exp (-eta * (n : ℝ) ^ (d : ℝ)⁻¹))) ≤
      ((n + 1 : ℕ) : ℝ) ^ r *
        (((k + 1 : ℕ) : ℝ) * 2 ^ k * ((2 * d + 1 : ℕ) : ℝ) ^ k *
          a⁻¹ ^ k * (1 - b)⁻¹ ^ k *
          (((n + 1 : ℕ) : ℝ) ^ k *
            Real.exp (-eta * (n : ℝ) ^ (d : ℝ)⁻¹))) := by
      gcongr
      exact hw n
    _ = C * (((n + 1 : ℕ) : ℝ) ^ (r + k) *
          Real.exp (-eta * (n : ℝ) ^ (d : ℝ)⁻¹)) := by
      rw [pow_add]
      dsimp [C]
      ring

theorem norm_weighted_iteratedDeriv_level_le_majorant
    {d : ℕ} {w : ℕ → ℝ} {a b eta : ℝ}
    (ha0 : 0 < a) (hb1 : b < 1)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta)
    (k n : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo a b) :
    ‖w n * iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) p‖ ≤
      weightedFiniteClusterDerivativeMajorant d w k a b eta n := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_iteratedDeriv_finiteClusterProbabilityPolynomialLevel_le_majorant
      ha0 hb1 hTail k n hp) (norm_nonneg (w n))

theorem weightedFiniteClusterProbabilityDerivativeSeries_hasDerivAt
    {d : ℕ} (hd : 0 < d) {w : ℕ → ℝ} {r : ℕ}
    (hw : ∀ n : ℕ, ‖w n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ r)
    {a b eta : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta)
    (k : ℕ) {p : ℝ} (hp : p ∈ Set.Ioo a b) :
    HasDerivAt (weightedFiniteClusterProbabilityDerivativeSeries d w k)
      (weightedFiniteClusterProbabilityDerivativeSeries d w (k + 1) p) p := by
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by dsimp [c]; constructor <;> linarith
  have hterm : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo a b →
      HasDerivAt
        (fun x ↦ w n * iteratedDeriv k
          (finiteClusterProbabilityPolynomialLevel d n) x)
        (w n * iteratedDeriv (k + 1)
          (finiteClusterProbabilityPolynomialLevel d n) y) y := by
    intro n y _hy
    have hdiff : Differentiable ℝ
        (iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n)) :=
      (finiteClusterProbabilityPolynomialLevel_contDiff d n).differentiable_iteratedDeriv
        k (by simp)
    have hhas := (hdiff y).hasDerivAt.const_mul (w n)
    simpa only [iteratedDeriv_succ] using hhas
  have hbase : Summable fun n : ℕ ↦
      w n * iteratedDeriv k (finiteClusterProbabilityPolynomialLevel d n) c := by
    exact (summable_weightedFiniteClusterDerivativeMajorant
      hd hw ha0 hb1 heta k).of_norm_bounded
        (fun n ↦ norm_weighted_iteratedDeriv_level_le_majorant
          ha0 hb1 hTail k n hc)
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (summable_weightedFiniteClusterDerivativeMajorant hd hw ha0 hb1 heta (k + 1))
    isOpen_Ioo isPreconnected_Ioo hterm
    (fun n y hy ↦ norm_weighted_iteratedDeriv_level_le_majorant
      ha0 hb1 hTail (k + 1) n hy)
    hc hbase hp
  simpa only [weightedFiniteClusterProbabilityDerivativeSeries] using hsum

theorem weightedFiniteClusterProbabilityDerivativeSeries_contDiffOn
    {d : ℕ} (hd : 0 < d) {w : ℕ → ℝ} {r : ℕ}
    (hw : ∀ n : ℕ, ‖w n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ r)
    {a b eta : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta)
    (k m : ℕ) :
    ContDiffOn ℝ m (weightedFiniteClusterProbabilityDerivativeSeries d w k)
      (Set.Ioo a b) := by
  induction m generalizing k with
  | zero =>
      change ContDiffOn ℝ (0 : WithTop ℕ∞)
        (weightedFiniteClusterProbabilityDerivativeSeries d w k) (Set.Ioo a b)
      rw [contDiffOn_zero]
      intro p hp
      exact (weightedFiniteClusterProbabilityDerivativeSeries_hasDerivAt
        hd hw ha0 hab hb1 heta hTail k hp).continuousAt.continuousWithinAt
  | succ m ih =>
      change ContDiffOn ℝ ((m : WithTop ℕ∞) + 1)
        (weightedFiniteClusterProbabilityDerivativeSeries d w k) (Set.Ioo a b)
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨?_, by simp, ?_⟩
      · intro p hp
        exact (weightedFiniteClusterProbabilityDerivativeSeries_hasDerivAt
          hd hw ha0 hab hb1 heta hTail k hp).differentiableAt.differentiableWithinAt
      · refine (ih (k + 1)).congr fun p hp ↦ ?_
        exact (weightedFiniteClusterProbabilityDerivativeSeries_hasDerivAt
          hd hw ha0 hab hb1 heta hTail k hp).deriv

theorem weightedFiniteClusterProbabilitySeries_contDiffOn_infty
    {d : ℕ} (hd : 0 < d) {w : ℕ → ℝ} {r : ℕ}
    (hw : ∀ n : ℕ, ‖w n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ r)
    {a b eta : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (weightedFiniteClusterProbabilityDerivativeSeries d w 0) (Set.Ioo a b) := by
  rw [contDiffOn_infty]
  exact fun m ↦ weightedFiniteClusterProbabilityDerivativeSeries_contDiffOn
    hd hw ha0 hab hb1 heta hTail 0 m

theorem natWeight_norm_le_succ (n : ℕ) :
    ‖(n : ℝ)‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (1 : ℕ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n), pow_one]
  exact_mod_cast Nat.le_succ n

theorem invNatWeight_norm_le_one (n : ℕ) :
    ‖1 / (n : ℝ)‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (0 : ℕ) := by
  simp only [pow_zero]
  cases n with
  | zero => simp
  | succ n =>
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hcast : (1 : ℝ) ≤ (n.succ : ℕ) := by
        exact_mod_cast Nat.succ_pos n
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hcast

theorem concreteSusceptibilitySeries_eq_weightedProbabilitySeries
    (d : ℕ) (p : ℝ) :
    concreteSusceptibilitySeries d p =
      weightedFiniteClusterProbabilityDerivativeSeries d (fun n ↦ (n : ℝ)) 0 p := by
  unfold concreteSusceptibilitySeries weightedFiniteClusterProbabilityDerivativeSeries
  apply tsum_congr
  intro n
  simp only [iteratedDeriv_zero]
  rfl

theorem concreteClusterDensityLevel_eq_invNat_mul_probabilityPolynomial
    {d : ℕ} (hd : 0 < d) (n : ℕ) (p : ℝ) :
    concreteClusterDensityLevel d n p =
      (1 / (n : ℝ)) * finiteClusterProbabilityPolynomialLevel d n p := by
  rw [concreteClusterDensityLevel_eq_sum_animals hd]
  unfold concreteAnimalDensityTerm finiteClusterProbabilityPolynomialLevel realAnimalWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

theorem concreteClusterDensitySeries_eq_weightedProbabilitySeries
    {d : ℕ} (hd : 0 < d) (p : ℝ) :
    concreteClusterDensitySeries d p =
      weightedFiniteClusterProbabilityDerivativeSeries d
        (fun n ↦ 1 / (n : ℝ)) 0 p := by
  unfold concreteClusterDensitySeries weightedFiniteClusterProbabilityDerivativeSeries
  apply tsum_congr
  intro n
  simp only [iteratedDeriv_zero]
  exact concreteClusterDensityLevel_eq_invNat_mul_probabilityPolynomial hd n p

/-- The susceptibility animal series is `C∞` on compact supercritical intervals under the
uniform finite-cluster tail input. -/
theorem concreteSusceptibilitySeries_contDiffOn_infty_of_uniform_stretchedExponential
    {d : ℕ} (hd : 0 < d) {a b eta : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteSusceptibilitySeries d) (Set.Ioo a b) := by
  have h := weightedFiniteClusterProbabilitySeries_contDiffOn_infty
    hd natWeight_norm_le_succ ha0 hab hb1 heta hTail
  exact h.congr fun p _hp ↦
    (concreteSusceptibilitySeries_eq_weightedProbabilitySeries d p).symm

/-- The finite-cluster density animal series is `C∞` on compact supercritical intervals under
the uniform finite-cluster tail input. -/
theorem concreteClusterDensitySeries_contDiffOn_infty_of_uniform_stretchedExponential
    {d : ℕ} (hd : 0 < d) {a b eta : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeProbabilityStretchedExponential d a b eta) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteClusterDensitySeries d) (Set.Ioo a b) := by
  have h := weightedFiniteClusterProbabilitySeries_contDiffOn_infty
    hd invNatWeight_norm_le_one ha0 hab hb1 heta hTail
  exact h.congr fun p _hp ↦
    concreteClusterDensitySeries_eq_weightedProbabilitySeries hd p

/-- **Grimmett, Theorem 8.92, interior analytic core.**

On every compact interval `[a,b] ⊂ (p_c,1)`, the uniform finite-cluster bound (8.91) makes the
real animal-series extensions of `θ`, `χᶠ`, and `κ` infinitely differentiable.  On physical
parameters these extensions equal respectively `theta`, `finiteSusceptibility.toReal`, and
`openClustersPerVertex`; see `thetaAnimalSeries_eq_theta`,
`concreteSusceptibilitySeries_eq_finiteSusceptibility_toReal`, and
`concreteClusterDensitySeries_eq_openClustersPerVertex`.

The source's one-sided endpoint `p = 1` uses the separate high-density topological estimate
(8.88), so it is intentionally not hidden in this interior theorem. -/
theorem theta_finiteSusceptibility_clusterDensity_contDiffOn_interior
    {d : ℕ} (hd : 2 ≤ d) {a b eta : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) (heta : 0 < eta)
    (hTail : UniformFiniteClusterSizeTailStretchedExponential d a b eta) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (thetaAnimalSeries d) (Set.Ioo a b) ∧
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteSusceptibilitySeries d) (Set.Ioo a b) ∧
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteClusterDensitySeries d) (Set.Ioo a b) := by
  have hProb := uniformFiniteClusterSizeProbability_of_tail hTail
  have hd0 : 0 < d := Nat.zero_lt_of_lt hd
  exact ⟨
    thetaAnimalSeries_contDiffOn_infty_of_uniform_stretchedExponential
      hd0 ha0 hab hb1 heta hProb,
    concreteSusceptibilitySeries_contDiffOn_infty_of_uniform_stretchedExponential
      hd0 ha0 hab hb1 heta hProb,
    concreteClusterDensitySeries_contDiffOn_infty_of_uniform_stretchedExponential
      hd0 ha0 hab hb1 heta hProb⟩

end

end Percolation
