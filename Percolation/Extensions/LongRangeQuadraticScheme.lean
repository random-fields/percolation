import Percolation.Extensions.LongRangeMultiscaleScheme

/-!
# A quadratic-scale Newman--Schulman scheme

At level `k` use `(N+k)^2` children and retain all but one.  The lost density has the
telescoping product `∏(1-1/(N+k)^2)`, while interval lengths grow like a squared rising
factorial.  This explicit choice avoids an opaque existence parameter in Theorem 12.8.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology unitInterval

/-- Quadratic arity at level `k`. -/
def longRangeQuadraticArity (N k : ℕ) : ℕ := (N + k) ^ 2

/-- Retain all but one child. -/
def longRangeQuadraticQuota (N k : ℕ) : ℕ := longRangeQuadraticArity N k - 1

/-- Interval lengths in the quadratic scheme. -/
def longRangeQuadraticLength (base N : ℕ) : ℕ → ℕ
  | 0 => base
  | k + 1 => longRangeQuadraticLength base N k * longRangeQuadraticArity N k

/-- Retained component targets in the quadratic scheme. -/
def longRangeQuadraticTarget (base N : ℕ) : ℕ → ℕ
  | 0 => base
  | k + 1 => longRangeQuadraticQuota N k * longRangeQuadraticTarget base N k

@[simp]
theorem longRangeQuadraticLength_zero (base N : ℕ) :
    longRangeQuadraticLength base N 0 = base := rfl

@[simp]
theorem longRangeQuadraticLength_succ (base N k : ℕ) :
    longRangeQuadraticLength base N (k + 1) =
      longRangeQuadraticLength base N k * longRangeQuadraticArity N k := rfl

@[simp]
theorem longRangeQuadraticTarget_zero (base N : ℕ) :
    longRangeQuadraticTarget base N 0 = base := rfl

@[simp]
theorem longRangeQuadraticTarget_succ (base N k : ℕ) :
    longRangeQuadraticTarget base N (k + 1) =
      longRangeQuadraticQuota N k * longRangeQuadraticTarget base N k := rfl

theorem longRangeQuadraticArity_pos {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    0 < longRangeQuadraticArity N k := by
  unfold longRangeQuadraticArity
  positivity

theorem longRangeQuadraticQuota_pos {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    0 < longRangeQuadraticQuota N k := by
  simp [longRangeQuadraticQuota, longRangeQuadraticArity]
  nlinarith

theorem longRangeQuadraticQuota_le_arity (N k : ℕ) :
    longRangeQuadraticQuota N k ≤ longRangeQuadraticArity N k :=
  Nat.sub_le _ _

theorem longRangeQuadraticLength_pos {base N : ℕ} (hbase : 0 < base)
    (hN : 2 ≤ N) : ∀ k, 0 < longRangeQuadraticLength base N k
  | 0 => hbase
  | k + 1 => Nat.mul_pos
      (longRangeQuadraticLength_pos hbase hN k)
      (longRangeQuadraticArity_pos hN k)

theorem longRangeQuadraticTarget_pos {base N : ℕ} (hbase : 0 < base)
    (hN : 2 ≤ N) : ∀ k, 0 < longRangeQuadraticTarget base N k
  | 0 => hbase
  | k + 1 => Nat.mul_pos
      (longRangeQuadraticQuota_pos hN k)
      (longRangeQuadraticTarget_pos hbase hN k)

/-- The explicit quadratic scheme. -/
def longRangeQuadraticScheme (base N : ℕ) (hbase : 0 < base) (hN : 2 ≤ N) :
    LongRangeMultiscaleScheme where
  length := longRangeQuadraticLength base N
  target := longRangeQuadraticTarget base N
  arity := longRangeQuadraticArity N
  quota := longRangeQuadraticQuota N
  length_succ := longRangeQuadraticLength_succ base N
  target_succ := longRangeQuadraticTarget_succ base N
  length_pos := longRangeQuadraticLength_pos hbase hN
  target_pos := longRangeQuadraticTarget_pos hbase hN
  arity_pos := longRangeQuadraticArity_pos hN
  quota_pos := longRangeQuadraticQuota_pos hN
  quota_le_arity := longRangeQuadraticQuota_le_arity N

/-- Exact telescoping identity for the retained fraction. -/
theorem quadratic_target_length_telescoping
    (base : ℕ) {N : ℕ} (hN : 2 ≤ N) : ∀ k,
    N * (N + k - 1) * longRangeQuadraticTarget base N k =
      (N - 1) * (N + k) * longRangeQuadraticLength base N k
  | 0 => by
      simp only [Nat.add_zero, longRangeQuadraticTarget_zero,
        longRangeQuadraticLength_zero]
      ac_rfl
  | k + 1 => by
      rw [longRangeQuadraticTarget_succ, longRangeQuadraticLength_succ]
      have ih := quadratic_target_length_telescoping base hN k
      simp only [longRangeQuadraticQuota, longRangeQuadraticArity]
      have hk : N + (k + 1) - 1 = N + k := by omega
      rw [hk]
      have hNk : 0 < N + k := by omega
      have hsq : (N + k) ^ 2 - 1 = (N + k - 1) * (N + k + 1) := by
        simpa [mul_comm] using (sq_tsub_sq (N + k) 1)
      rw [hsq]
      calc
        N * (N + k) * ((N + k - 1) * (N + k + 1) *
            longRangeQuadraticTarget base N k) =
            (N * (N + k - 1) * longRangeQuadraticTarget base N k) *
              ((N + k) * (N + k + 1)) := by ring
        _ = ((N - 1) * (N + k) * longRangeQuadraticLength base N k) *
              ((N + k) * (N + k + 1)) := by rw [ih]
        _ = (N - 1) * (N + (k + 1)) *
            (longRangeQuadraticLength base N k * (N + k) ^ 2) := by
          rw [show N + (k + 1) = N + k + 1 by omega]
          ring

/-- Uniform positive retained density: at least `(N-1)/N` of every block target. -/
theorem quadratic_target_density_lower
    {base N : ℕ} (hbase : 0 < base) (hN : 2 ≤ N) (k : ℕ) :
    ((N - 1 : ℕ) : ℝ) / N ≤
      (longRangeQuadraticTarget base N k : ℝ) /
        longRangeQuadraticLength base N k := by
  have hid := quadratic_target_length_telescoping base hN k
  have hL : 0 < longRangeQuadraticLength base N k :=
    longRangeQuadraticLength_pos hbase hN k
  have hNk : 0 < N + k - 1 := by omega
  have hNpos : 0 < (N : ℝ) := by positivity
  have hLpos : 0 < (longRangeQuadraticLength base N k : ℝ) := by positivity
  have hden : 0 < (N : ℝ) * (longRangeQuadraticLength base N k : ℝ) :=
    mul_pos hNpos hLpos
  rw [div_le_div_iff₀ hNpos hLpos]
  have hnat : (N - 1) * longRangeQuadraticLength base N k ≤
      N * longRangeQuadraticTarget base N k := by
    have hfactor : N + k - 1 ≤ N + k := by omega
    apply Nat.le_of_mul_le_mul_right (c := N + k - 1) _ hNk
    calc
      ((N - 1) * longRangeQuadraticLength base N k) * (N + k - 1) ≤
          ((N - 1) * longRangeQuadraticLength base N k) * (N + k) :=
        Nat.mul_le_mul_left _ hfactor
      _ = (N - 1) * (N + k) * longRangeQuadraticLength base N k := by
        ac_rfl
      _ = N * (N + k - 1) * longRangeQuadraticTarget base N k := hid.symm
      _ = (N * longRangeQuadraticTarget base N k) * (N + k - 1) := by
        ac_rfl
  have hreal : ((N - 1 : ℕ) : ℝ) * longRangeQuadraticLength base N k ≤
      (N : ℝ) * longRangeQuadraticTarget base N k := by
    exact_mod_cast hnat
  simpa [mul_comm] using hreal

end Percolation
