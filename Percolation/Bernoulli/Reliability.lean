import Percolation.Bernoulli.FKG
import Percolation.Bernoulli.Russo
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Real.Sqrt

/-!
# The reliability-theory inequalities

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.5, Theorems (2.34), (2.36), (2.38) and
equations (2.35), (2.37), (2.39), (2.41), (2.44), pp. 46–49
(source id `grimmett-percolation-1999`).

This file develops the reliability-theory estimates of §2.5 on the finite cube model of
`Percolation.Bernoulli.FiniteCube` and transfers them to the ambient product measure:

* `Percolation.finiteOpenCount`, `Percolation.finiteBernoulliCovariance`,
  `Percolation.finiteBernoulliVariance` — Grimmett's open-coordinate count `N(ω)` and the
  covariance and variance of finite-cube observables, with the binomial moments
  `Percolation.finiteBernoulliExpectation_finiteOpenCount` (`E_p(N) = mp`) and
  `Percolation.finiteBernoulliVariance_finiteOpenCount` (`var(N) = mp(1-p)`);
* `Percolation.hasDerivAt_finiteBernoulliWeight` and
  `Percolation.hasDerivAt_finiteBernoulliProbability_covariance` — **Theorem (2.34)**,
  equation (2.35): `d/dp P_p(A) = cov(N, 1_A) / (p(1-p))` for **arbitrary** trace events
  (no monotonicity), with measure-level form
  `Percolation.DependsOn.hasDerivAt_setBernoulli_real_covariance` and cubic wrapper
  `Percolation.DependsOn.bernoulliBondMeasure_real_covariance_hasDerivAt`;
* `Percolation.finiteBernoulliCovariance_sq_le` (the Cauchy–Schwarz inequality for the
  finite-cube covariance) and `Percolation.abs_finiteBernoulliCovariance_div_le_sqrt` —
  **Theorem (2.36)(a)**: `|dP_p(A)/dp| ≤ √(m P_p(A)(1 - P_p(A)) / (p(1-p)))`;
* `Percolation.finiteBernoulliProbability_mul_one_sub_le_finiteBernoulliCovariance` and
  `Percolation.finiteBernoulliProbability_mul_one_sub_div_le_finiteBernoulliCovariance_div`
  — **Theorem (2.36)(b)** via equation (2.41): for increasing events
  `P_p(A)(1 - P_p(A)) / (p(1-p)) ≤ dP_p(A)/dp`, from the FKG inequality applied to the
  increasing observables `N - 1_A` and `1_A`;
* `Percolation.rpow_add_rpow_le_rpow_add_rpow_of_le` and
  `Percolation.grimmett_scalar_244` — the scalar inequality (2.44)
  `x^γ p^γ + y^γ (1 - p^γ) ≤ (xp + y(1-p))^γ` for `0 ≤ y ≤ x`, `p ∈ [0,1]`, `γ ≥ 1`,
  reduced to the convexity-increment inequality for `t ↦ t^γ` proved by the mean value
  theorem;
* `Percolation.finiteBernoulliProbability_rpow_le` — **Theorem (2.38)**, inequality (2.39)
  in the form `P_{p^γ}(A) ≤ P_p(A)^γ`, by induction on the support using (2.44);
* `Percolation.DependsOn.setBernoulli_real_rpow_le`,
  `Percolation.DependsOn.setBernoulli_real_logRatio_antitone` and the cubic wrapper
  `Percolation.DependsOn.bernoulliBondMeasure_real_logRatio_antitone` — the measure-level
  Theorem (2.38): for an increasing finitely supported event, `log P_p(A) / log p` is
  non-increasing in `p` on `(0, 1)`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped Finset unitInterval

variable {ι : Type*}

/-! ### The open count and the finite covariance -/

/-- Grimmett's random variable `N(ω)`, the number of open coordinates, as a real observable
on the finite cube: on the powerset of the support `E` the trace `s` consists exactly of the
open coordinates, so the count is the cardinality (p. 47). -/
def finiteOpenCount (s : Finset ι) : ℝ :=
  (s.card : ℝ)

/-- Covariance of two observables on the finite cube `{0,1}^E`:
`cov(X, Y) = E_p(XY) - E_p(X)E_p(Y)`. -/
def finiteBernoulliCovariance (E : Finset ι) (p : ℝ) (X Y : Finset ι → ℝ) : ℝ :=
  finiteBernoulliExpectation E p (fun s => X s * Y s) -
    finiteBernoulliExpectation E p X * finiteBernoulliExpectation E p Y

/-- Variance of an observable on the finite cube. -/
def finiteBernoulliVariance (E : Finset ι) (p : ℝ) (X : Finset ι → ℝ) : ℝ :=
  finiteBernoulliCovariance E p X X

/-- The finite probability read as the expectation of the indicator (definitional). -/
private theorem probability_eq_expectation_indicator (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliExpectation E p (T.indicator fun _ => (1 : ℝ)) =
      finiteBernoulliProbability E p T :=
  rfl

/-- Indicators are idempotent under multiplication: `E_p(1_T · 1_T) = P_p(T)`. -/
private theorem expectation_indicator_mul_self (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliExpectation E p
      (fun s => T.indicator (fun _ => (1 : ℝ)) s * T.indicator (fun _ => (1 : ℝ)) s) =
      finiteBernoulliProbability E p T := by
  rw [← probability_eq_expectation_indicator]
  exact finiteBernoulliExpectation_congr fun s _ => by
    by_cases hs : s ∈ T <;> simp [hs]

/-! ### Moments of the open count -/

/-- The binomial mean `E_p(N) = |E| p`, valid for every real density. -/
theorem finiteBernoulliExpectation_finiteOpenCount (E : Finset ι) (p : ℝ) :
    finiteBernoulliExpectation E p finiteOpenCount = E.card * p := by
  classical
  induction E using Finset.induction with
  | empty =>
      simp [finiteBernoulliExpectation, finiteBernoulliWeight, finiteOpenCount]
  | insert a E ha ih =>
      rw [finiteBernoulliExpectation_insert ha]
      have h1 : finiteBernoulliExpectation E p (fun s => finiteOpenCount (insert a s)) =
          finiteBernoulliExpectation E p (fun s => finiteOpenCount s + 1) :=
        finiteBernoulliExpectation_congr fun s hs => by
          have has : a ∉ s := fun h => ha (Finset.mem_powerset.mp hs h)
          rw [finiteOpenCount, finiteOpenCount, Finset.card_insert_of_notMem has,
            Nat.cast_add, Nat.cast_one]
      rw [h1, finiteBernoulliExpectation_add, finiteBernoulliExpectation_const, ih,
        Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      ring

/-- The binomial second moment `E_p(N²) = |E| p + |E|(|E| - 1) p²`, valid for every real
density. -/
theorem finiteBernoulliExpectation_finiteOpenCount_mul_self (E : Finset ι) (p : ℝ) :
    finiteBernoulliExpectation E p (fun s => finiteOpenCount s * finiteOpenCount s) =
      E.card * p + E.card * (E.card - 1) * p ^ 2 := by
  classical
  induction E using Finset.induction with
  | empty =>
      simp [finiteBernoulliExpectation, finiteBernoulliWeight, finiteOpenCount]
  | insert a E ha ih =>
      rw [finiteBernoulliExpectation_insert ha]
      have h1 : finiteBernoulliExpectation E p
          (fun s => finiteOpenCount (insert a s) * finiteOpenCount (insert a s)) =
          finiteBernoulliExpectation E p
            (fun s => finiteOpenCount s * finiteOpenCount s + (2 * finiteOpenCount s + 1)) :=
        finiteBernoulliExpectation_congr fun s hs => by
          have has : a ∉ s := fun h => ha (Finset.mem_powerset.mp hs h)
          rw [finiteOpenCount, finiteOpenCount, Finset.card_insert_of_notMem has,
            Nat.cast_add, Nat.cast_one]
          ring
      rw [h1, finiteBernoulliExpectation_add, finiteBernoulliExpectation_add,
        finiteBernoulliExpectation_const_mul, finiteBernoulliExpectation_const,
        finiteBernoulliExpectation_finiteOpenCount, ih,
        Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      ring

/-- The binomial variance `var(N) = |E| p (1 - p)`, valid for every real density. -/
theorem finiteBernoulliVariance_finiteOpenCount (E : Finset ι) (p : ℝ) :
    finiteBernoulliVariance E p finiteOpenCount = E.card * p * (1 - p) := by
  rw [finiteBernoulliVariance, finiteBernoulliCovariance,
    finiteBernoulliExpectation_finiteOpenCount_mul_self,
    finiteBernoulliExpectation_finiteOpenCount]
  ring

/-- The indicator variance `var(1_T) = P_p(T)(1 - P_p(T))`, valid for every real density. -/
theorem finiteBernoulliVariance_indicator (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliVariance E p (T.indicator fun _ => 1) =
      finiteBernoulliProbability E p T * (1 - finiteBernoulliProbability E p T) := by
  rw [finiteBernoulliVariance, finiteBernoulliCovariance, expectation_indicator_mul_self,
    probability_eq_expectation_indicator]
  ring

/-! ### The covariance as a central moment and Cauchy–Schwarz -/

/-- The covariance as a central second moment:
`cov(X, Y) = E_p((X - E_p X)(Y - E_p Y))`. -/
theorem finiteBernoulliCovariance_eq_expectation_mul_sub (E : Finset ι) (p : ℝ)
    (X Y : Finset ι → ℝ) :
    finiteBernoulliCovariance E p X Y =
      finiteBernoulliExpectation E p (fun s =>
        (X s - finiteBernoulliExpectation E p X) *
          (Y s - finiteBernoulliExpectation E p Y)) := by
  rw [finiteBernoulliCovariance, finiteBernoulliExpectation_sub_const_mul]
  ring

/-- **Cauchy–Schwarz for the finite-cube covariance**:
`cov(X, Y)² ≤ var(X) var(Y)`, by the finite Cauchy–Schwarz inequality applied to the
weighted vectors `√w (X - E_p X)` and `√w (Y - E_p Y)`. -/
theorem finiteBernoulliCovariance_sq_le {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X Y : Finset ι → ℝ) :
    finiteBernoulliCovariance E p X Y ^ 2 ≤
      finiteBernoulliVariance E p X * finiteBernoulliVariance E p Y := by
  have hw : ∀ s : Finset ι, 0 ≤ finiteBernoulliWeight E p s :=
    finiteBernoulliWeight_nonneg hp0 hp1
  have h1 : finiteBernoulliCovariance E p X Y =
      ∑ s ∈ E.powerset,
        (Real.sqrt (finiteBernoulliWeight E p s) *
            (X s - finiteBernoulliExpectation E p X)) *
          (Real.sqrt (finiteBernoulliWeight E p s) *
            (Y s - finiteBernoulliExpectation E p Y)) := by
    rw [finiteBernoulliCovariance_eq_expectation_mul_sub]
    exact Finset.sum_congr rfl fun s _ => by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw s)]
  have h2 : finiteBernoulliVariance E p X =
      ∑ s ∈ E.powerset,
        (Real.sqrt (finiteBernoulliWeight E p s) *
          (X s - finiteBernoulliExpectation E p X)) ^ 2 := by
    rw [finiteBernoulliVariance, finiteBernoulliCovariance_eq_expectation_mul_sub]
    exact Finset.sum_congr rfl fun s _ => by
      rw [mul_pow, Real.sq_sqrt (hw s), pow_two]
  have h3 : finiteBernoulliVariance E p Y =
      ∑ s ∈ E.powerset,
        (Real.sqrt (finiteBernoulliWeight E p s) *
          (Y s - finiteBernoulliExpectation E p Y)) ^ 2 := by
    rw [finiteBernoulliVariance, finiteBernoulliCovariance_eq_expectation_mul_sub]
    exact Finset.sum_congr rfl fun s _ => by
      rw [mul_pow, Real.sq_sqrt (hw s), pow_two]
  calc finiteBernoulliCovariance E p X Y ^ 2
      = (∑ s ∈ E.powerset,
          (Real.sqrt (finiteBernoulliWeight E p s) *
              (X s - finiteBernoulliExpectation E p X)) *
            (Real.sqrt (finiteBernoulliWeight E p s) *
              (Y s - finiteBernoulliExpectation E p Y))) ^ 2 := by rw [h1]
    _ ≤ (∑ s ∈ E.powerset,
          (Real.sqrt (finiteBernoulliWeight E p s) *
            (X s - finiteBernoulliExpectation E p X)) ^ 2) *
          ∑ s ∈ E.powerset,
            (Real.sqrt (finiteBernoulliWeight E p s) *
              (Y s - finiteBernoulliExpectation E p Y)) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = finiteBernoulliVariance E p X * finiteBernoulliVariance E p Y := by rw [h2, h3]

/-! ### Theorem 2.34: the covariance form of the derivative -/

/-- Auxiliary cast identity: `k u^(k-1) = k u^k / u` for `u ≠ 0`, absorbing the truncated
natural subtraction in the exponent. -/
private theorem cast_mul_pow_pred {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    (k : ℝ) * u ^ (k - 1) = (k : ℝ) * u ^ k / u := by
  cases k with
  | zero => simp
  | succ n =>
      rw [Nat.add_sub_cancel, pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hu]

/-- **The derivative of the Bernoulli weight** in the density: for `0 < p < 1` and `s ⊆ E`,
`d/dp [p^{|s|} (1-p)^{|E|-|s|}] = ((|s| - |E| p) / (p(1-p))) · p^{|s|} (1-p)^{|E|-|s|}` —
the summand computation in Grimmett's proof of Theorem (2.34) (p. 47). -/
theorem hasDerivAt_finiteBernoulliWeight {E : Finset ι} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) {s : Finset ι} (hs : s ⊆ E) :
    HasDerivAt (fun x : ℝ => finiteBernoulliWeight E x s)
      (((s.card : ℝ) - E.card * p) / (p * (1 - p)) * finiteBernoulliWeight E p s) p := by
  have hp : p ≠ 0 := hp0.ne'
  have hq0 : (0 : ℝ) < 1 - p := by linarith
  have hq : (1 : ℝ) - p ≠ 0 := hq0.ne'
  have hbase : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) p := by
    simpa using (hasDerivAt_id p).const_sub (1 : ℝ)
  have h := (hasDerivAt_pow s.card p).mul (hbase.fun_pow (E.card - s.card))
  have hfun : (fun x : ℝ => finiteBernoulliWeight E x s) =
      fun x : ℝ => x ^ s.card * (1 - x) ^ (E.card - s.card) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have hcast : ((E.card - s.card : ℕ) : ℝ) = (E.card : ℝ) - s.card :=
    Nat.cast_sub (Finset.card_le_card hs)
  rw [finiteBernoulliWeight, cast_mul_pow_pred hp s.card,
    cast_mul_pow_pred hq (E.card - s.card), hcast]
  field_simp
  ring

/-- **Theorem (2.34), finite form (equation (2.35)).** For an **arbitrary** trace event `T`
and `0 < p < 1`, the map `p ↦ P_p(T)` is differentiable with
`d/dp P_p(T) = cov(N, 1_T) / (p(1-p))` where `N` is the number of open coordinates. No
monotonicity of `T` is assumed. -/
theorem hasDerivAt_finiteBernoulliProbability_covariance {E : Finset ι} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (T : Set (Finset ι)) :
    HasDerivAt (fun x : ℝ => finiteBernoulliProbability E x T)
      (finiteBernoulliCovariance E p finiteOpenCount (T.indicator fun _ => 1) /
        (p * (1 - p))) p := by
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ s ∈ E.powerset,
        finiteBernoulliWeight E x s * T.indicator (fun _ => (1 : ℝ)) s)
      (∑ s ∈ E.powerset, ((s.card : ℝ) - E.card * p) / (p * (1 - p)) *
        finiteBernoulliWeight E p s * T.indicator (fun _ => (1 : ℝ)) s) p :=
    HasDerivAt.fun_sum fun s hs =>
      (hasDerivAt_finiteBernoulliWeight hp0 hp1 (Finset.mem_powerset.mp hs)).mul_const _
  have hderiv : (∑ s ∈ E.powerset, ((s.card : ℝ) - E.card * p) / (p * (1 - p)) *
      finiteBernoulliWeight E p s * T.indicator (fun _ => (1 : ℝ)) s) =
      finiteBernoulliCovariance E p finiteOpenCount (T.indicator fun _ => 1) /
        (p * (1 - p)) := by
    have h1 : (∑ s ∈ E.powerset, ((s.card : ℝ) - E.card * p) / (p * (1 - p)) *
        finiteBernoulliWeight E p s * T.indicator (fun _ => (1 : ℝ)) s) =
        finiteBernoulliExpectation E p (fun s => (p * (1 - p))⁻¹ *
          (finiteOpenCount s * T.indicator (fun _ => (1 : ℝ)) s +
            -((E.card : ℝ) * p) * T.indicator (fun _ => (1 : ℝ)) s)) :=
      Finset.sum_congr rfl fun s _ => by
        simp only [finiteOpenCount]
        ring
    rw [h1, finiteBernoulliExpectation_const_mul, finiteBernoulliExpectation_add,
      finiteBernoulliExpectation_const_mul, finiteBernoulliCovariance,
      finiteBernoulliExpectation_finiteOpenCount, div_eq_inv_mul]
    ring
  have hfun : (fun x : ℝ => finiteBernoulliProbability E x T) =
      fun x : ℝ => ∑ s ∈ E.powerset,
        finiteBernoulliWeight E x s * T.indicator (fun _ => (1 : ℝ)) s := rfl
  rw [hfun]
  exact hsum.congr_deriv hderiv

/-- **Theorem (2.34), measure level.** The probability of a finitely supported event —
increasing or not — is differentiable in the density, with derivative
`cov(N, 1_A) / (p(1-p))` computed on the finite cube. The density is clamped to `[0,1]` by
`Set.projIcc`, exactly as in `IsIncreasingEvent.hasDerivAt_setBernoulli_real`. -/
theorem DependsOn.hasDerivAt_setBernoulli_real_covariance {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasDerivAt
      (fun x : ℝ => setBer((Set.univ : Set ι), Set.projIcc 0 1 zero_le_one x).real A)
      (finiteBernoulliCovariance E (p : ℝ) finiteOpenCount
        ((eventTrace A).indicator fun _ => 1) / ((p : ℝ) * (1 - (p : ℝ)))) (p : ℝ) := by
  have hfin := hasDerivAt_finiteBernoulliProbability_covariance (E := E) hp0 hp1
    (eventTrace A)
  refine hfin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hp0 hp1] with x hx
  have hcoe : ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ) = x := by
    rw [Set.coe_projIcc, min_eq_right hx.2.le, max_eq_right hx.1.le]
  rw [hA.setBernoulli_real_eq_finiteBernoulliProbability (Set.projIcc 0 1 zero_le_one x),
    hcoe]

/-- Theorem (2.34) for the cubic-lattice Bernoulli bond measure. -/
theorem DependsOn.bernoulliBondMeasure_real_covariance_hasDerivAt {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)} (hA : DependsOn E A) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasDerivAt
      (fun x : ℝ => (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one x)).real A)
      (finiteBernoulliCovariance E (p : ℝ) finiteOpenCount
        ((eventTrace A).indicator fun _ => 1) / ((p : ℝ) * (1 - (p : ℝ)))) (p : ℝ) := by
  simpa [bernoulliBondMeasure] using hA.hasDerivAt_setBernoulli_real_covariance hp0 hp1

/-! ### Theorem 2.36(a): the square-root upper bound -/

/-- **Theorem (2.36)(a), finite form.** For an arbitrary trace event and `0 < p < 1`, the
covariance form of the derivative (Theorem (2.34)) is bounded by
`√(m P_p(T)(1 - P_p(T)) / (p(1-p)))` with `m = |E|` — Cauchy–Schwarz together with the
binomial and indicator variances. -/
theorem abs_finiteBernoulliCovariance_div_le_sqrt {E : Finset ι} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (T : Set (Finset ι)) :
    |finiteBernoulliCovariance E p finiteOpenCount (T.indicator fun _ => 1) /
        (p * (1 - p))| ≤
      Real.sqrt ((E.card : ℝ) * finiteBernoulliProbability E p T *
        (1 - finiteBernoulliProbability E p T) / (p * (1 - p))) := by
  have hp : p ≠ 0 := hp0.ne'
  have hq0 : (0 : ℝ) < 1 - p := by linarith
  have hq : (1 : ℝ) - p ≠ 0 := hq0.ne'
  have hCS := finiteBernoulliCovariance_sq_le (E := E) hp0.le hp1.le finiteOpenCount
    (T.indicator fun _ => (1 : ℝ))
  rw [finiteBernoulliVariance_finiteOpenCount, finiteBernoulliVariance_indicator] at hCS
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  rw [div_pow]
  refine (div_le_div_of_nonneg_right hCS (sq_nonneg (p * (1 - p)))).trans_eq ?_
  field_simp

/-! ### Theorem 2.36(b): the variance lower bound via FKG -/

/-- **Equation (2.41).** For an increasing trace event,
`P_p(T)(1 - P_p(T)) ≤ cov(N, 1_T)`: writing `cov(N, 1_T) = cov(N - 1_T, 1_T) + var(1_T)`,
the first term is nonnegative by FKG because both `N - 1_T` and `1_T` are monotone on the
powerset (the count jumps by at least one along a strict inclusion while the indicator jumps
by at most one). -/
theorem finiteBernoulliProbability_mul_one_sub_le_finiteBernoulliCovariance {E : Finset ι}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T : Set (Finset ι)} (hT : IsIncreasingTrace T) :
    finiteBernoulliProbability E p T * (1 - finiteBernoulliProbability E p T) ≤
      finiteBernoulliCovariance E p finiteOpenCount (T.indicator fun _ => 1) := by
  have hg : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E →
      T.indicator (fun _ => (1 : ℝ)) s ≤ T.indicator (fun _ => (1 : ℝ)) t := by
    intro s t hst _
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hT hst hs)]
    · rw [Set.indicator_of_notMem hs]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have hf : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E →
      finiteOpenCount s - T.indicator (fun _ => (1 : ℝ)) s ≤
        finiteOpenCount t - T.indicator (fun _ => (1 : ℝ)) t := by
    intro s t hst _
    rcases eq_or_ne s t with rfl | hne
    · exact le_rfl
    · have hlt : s.card < t.card := Finset.card_lt_card (hst.ssubset_of_ne hne)
      have hcard : (s.card : ℝ) + 1 ≤ (t.card : ℝ) := by exact_mod_cast hlt
      have h1 : T.indicator (fun _ => (1 : ℝ)) t ≤ 1 :=
        Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
      have h2 : 0 ≤ T.indicator (fun _ => (1 : ℝ)) s :=
        Set.indicator_apply_nonneg fun _ => zero_le_one
      rw [finiteOpenCount, finiteOpenCount]
      linarith
  have hfkg := finiteBernoulliExpectation_mul_fkg_of_monotone hp0 hp1
    (f := fun s => finiteOpenCount s - T.indicator (fun _ => (1 : ℝ)) s)
    (g := T.indicator fun _ => (1 : ℝ)) hf hg
  have hEprod : finiteBernoulliExpectation E p
      (fun s => (finiteOpenCount s - T.indicator (fun _ => (1 : ℝ)) s) *
        T.indicator (fun _ => (1 : ℝ)) s) =
      finiteBernoulliExpectation E p
        (fun s => finiteOpenCount s * T.indicator (fun _ => (1 : ℝ)) s) -
        finiteBernoulliProbability E p T := by
    rw [finiteBernoulliExpectation_congr
        (Y := fun s => finiteOpenCount s * T.indicator (fun _ => (1 : ℝ)) s -
          T.indicator (fun _ => (1 : ℝ)) s * T.indicator (fun _ => (1 : ℝ)) s)
        fun s _ => by ring,
      finiteBernoulliExpectation_sub, expectation_indicator_mul_self]
  rw [finiteBernoulliExpectation_sub, probability_eq_expectation_indicator, hEprod] at hfkg
  rw [finiteBernoulliCovariance, probability_eq_expectation_indicator]
  nlinarith [hfkg]

/-- **Theorem (2.36)(b), finite form (equation (2.37)).** For an increasing trace event and
`0 < p < 1`, the covariance form of the derivative (Theorem (2.34)) is at least
`P_p(T)(1 - P_p(T)) / (p(1-p))`. -/
theorem finiteBernoulliProbability_mul_one_sub_div_le_finiteBernoulliCovariance_div
    {E : Finset ι} {p : ℝ} {T : Set (Finset ι)} (hT : IsIncreasingTrace T)
    (hp0 : 0 < p) (hp1 : p < 1) :
    finiteBernoulliProbability E p T * (1 - finiteBernoulliProbability E p T) /
        (p * (1 - p)) ≤
      finiteBernoulliCovariance E p finiteOpenCount (T.indicator fun _ => 1) /
        (p * (1 - p)) :=
  div_le_div_of_nonneg_right
    (finiteBernoulliProbability_mul_one_sub_le_finiteBernoulliCovariance hp0.le hp1.le hT)
    (mul_pos hp0 (by linarith)).le

/-! ### The scalar inequality (2.44) -/

/-- Convexity-increment inequality for real powers: for `γ ≥ 1`, `c ≥ 0` and `0 ≤ a ≤ b`,
`b^γ + (a+c)^γ ≤ a^γ + (b+c)^γ`. The map `t ↦ (t+c)^γ - t^γ` is monotone on `[0, ∞)`
because its derivative `γ((t+c)^{γ-1} - t^{γ-1})` is nonnegative. -/
theorem rpow_add_rpow_le_rpow_add_rpow_of_le {a b c γ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hγ : 1 ≤ γ) :
    b ^ γ + (a + c) ^ γ ≤ a ^ γ + (b + c) ^ γ := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (u + c) ^ γ - u ^ γ)
      (γ * (t + c) ^ (γ - 1) - γ * t ^ (γ - 1)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => (u + c) ^ γ) (γ * (t + c) ^ (γ - 1)) t := by
      have hcomp := (Real.hasDerivAt_rpow_const (x := t + c) (Or.inr hγ)).comp t
        ((hasDerivAt_id t).add_const c)
      simpa using hcomp
    exact h1.sub (Real.hasDerivAt_rpow_const (Or.inr hγ))
  have hmono : MonotoneOn (fun t : ℝ => (t + c) ^ γ - t ^ γ) (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun t => γ * (t + c) ^ (γ - 1) - γ * t ^ (γ - 1))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht0 : (0 : ℝ) < t := ht
    have hle : t ^ (γ - 1) ≤ (t + c) ^ (γ - 1) :=
      Real.rpow_le_rpow ht0.le (by linarith) (by linarith)
    have hγ0 : (0 : ℝ) ≤ γ := by linarith
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hle hγ0)
  have h := hmono (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab
  linarith [h]

/-- **The scalar inequality (2.44)** (Grimmett p. 49): for `0 ≤ y ≤ x`, `p ∈ [0,1]` and
`γ ≥ 1`, `x^γ p^γ + y^γ (1 - p^γ) ≤ (xp + y(1-p))^γ`. Since `y^γ (1 - p^γ) = y^γ - (yp)^γ`
and `y = yp + y(1-p)`, this is the convexity-increment inequality
`rpow_add_rpow_le_rpow_add_rpow_of_le` with `a = yp ≤ b = xp` and `c = y(1-p)`. -/
theorem grimmett_scalar_244 {x y p : ℝ} {γ : ℝ} (hxy : y ≤ x) (hy : 0 ≤ y)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hγ : 1 ≤ γ) :
    x ^ γ * p ^ γ + y ^ γ * (1 - p ^ γ) ≤ (x * p + y * (1 - p)) ^ γ := by
  have hx : 0 ≤ x := hy.trans hxy
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  have key := rpow_add_rpow_le_rpow_add_rpow_of_le (a := y * p) (b := x * p)
    (c := y * (1 - p)) (mul_nonneg hy hp0) (mul_le_mul_of_nonneg_right hxy hp0)
    (mul_nonneg hy h1p) hγ
  rw [show y * p + y * (1 - p) = y from by ring, Real.mul_rpow hx hp0,
    Real.mul_rpow hy hp0] at key
  rw [show y ^ γ * (1 - p ^ γ) = y ^ γ - y ^ γ * p ^ γ from by ring]
  linarith [key]

/-! ### Theorem 2.38: the power inequality (2.39) -/

/-- **Theorem (2.38), finite form (inequality (2.39)).** For an increasing trace event,
`0 < p < 1` and `γ ≥ 1`, `P_{p^γ}(T) ≤ P_p(T)^γ`, by induction on the support: the
one-coordinate insert split turns the induction step into the scalar inequality (2.44)
applied to the two increasing sections. -/
theorem finiteBernoulliProbability_rpow_le {E : Finset ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace T) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {γ : ℝ} (hγ : 1 ≤ γ) :
    finiteBernoulliProbability E (p ^ γ) T ≤ finiteBernoulliProbability E p T ^ γ := by
  classical
  induction E using Finset.induction generalizing T hT with
  | empty =>
      have hval : ∀ x : ℝ, finiteBernoulliProbability (∅ : Finset ι) x T =
          T.indicator (fun _ => (1 : ℝ)) ∅ := fun x => by
        simp [finiteBernoulliProbability, finiteBernoulliExpectation, finiteBernoulliWeight]
      rw [hval, hval]
      by_cases h : (∅ : Finset ι) ∈ T
      · rw [Set.indicator_of_mem h, Real.one_rpow]
      · rw [Set.indicator_of_notMem h, Real.zero_rpow (one_pos.trans_le hγ).ne']
  | insert a E ha ih =>
      have hT₁ : IsIncreasingTrace {s : Finset ι | insert a s ∈ T} := fun s t hst hs =>
        hT (Finset.insert_subset_insert a hst) hs
      have hsub : finiteBernoulliProbability E p T ≤
          finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} :=
        finiteBernoulliProbability_mono hp0.le hp1.le fun s hs =>
          hT (Finset.subset_insert a s) hs
      have hq0 : (0 : ℝ) ≤ p ^ γ := (Real.rpow_pos_of_pos hp0 γ).le
      have hq1 : p ^ γ ≤ 1 := Real.rpow_le_one hp0.le hp1.le (by linarith)
      rw [finiteBernoulliProbability_insert ha, finiteBernoulliProbability_insert ha]
      calc p ^ γ * finiteBernoulliProbability E (p ^ γ) {s : Finset ι | insert a s ∈ T} +
            (1 - p ^ γ) * finiteBernoulliProbability E (p ^ γ) T
          ≤ p ^ γ *
              finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} ^ γ +
            (1 - p ^ γ) * finiteBernoulliProbability E p T ^ γ :=
            add_le_add (mul_le_mul_of_nonneg_left (ih hT₁) hq0)
              (mul_le_mul_of_nonneg_left (ih hT) (by linarith))
        _ = finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} ^ γ * p ^ γ +
            finiteBernoulliProbability E p T ^ γ * (1 - p ^ γ) := by ring
        _ ≤ (finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} * p +
              finiteBernoulliProbability E p T * (1 - p)) ^ γ :=
            grimmett_scalar_244 hsub
              (finiteBernoulliProbability_nonneg hp0.le hp1.le T) hp0.le hp1.le hγ
        _ = (p * finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} +
              (1 - p) * finiteBernoulliProbability E p T) ^ γ := by
            rw [show finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} * p +
                  finiteBernoulliProbability E p T * (1 - p) =
                p * finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} +
                  (1 - p) * finiteBernoulliProbability E p T from by ring]

/-- On a fixed support, a trace event that is null at one nondegenerate density is null at
every density: the weights are strictly positive, so nullity forces the indicator to vanish
on the whole powerset. -/
theorem finiteBernoulliProbability_eq_zero_of_eq_zero {E : Finset ι} {T : Set (Finset ι)}
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h : finiteBernoulliProbability E p T = 0) (q : ℝ) :
    finiteBernoulliProbability E q T = 0 := by
  rw [finiteBernoulliProbability_eq_sum_indicator] at h ⊢
  have hnn : ∀ s ∈ E.powerset,
      0 ≤ finiteBernoulliWeight E p s * T.indicator (fun _ => (1 : ℝ)) s := fun s _ =>
    mul_nonneg (finiteBernoulliWeight_nonneg hp0.le hp1.le s)
      (Set.indicator_apply_nonneg fun _ => zero_le_one)
  refine Finset.sum_eq_zero fun s hs => ?_
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h s hs
  rcases mul_eq_zero.mp hzero with hw | hind
  · exact absurd hw (finiteBernoulliWeight_pos hp0 hp1 s).ne'
  · rw [hind, mul_zero]

/-- **Theorem (2.38), measure level, power form (inequality (2.39)).** For an increasing
finitely supported event and densities `q = p^γ` with `0 < p < 1`, `γ ≥ 1`:
`P_{p^γ}(A) ≤ P_p(A)^γ`. -/
theorem DependsOn.setBernoulli_real_rpow_le {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (hAinc : IsIncreasingEvent A) {p q : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {γ : ℝ} (hγ : 1 ≤ γ)
    (hq : (q : ℝ) = (p : ℝ) ^ γ) :
    setBer((Set.univ : Set ι), q).real A ≤ setBer((Set.univ : Set ι), p).real A ^ γ := by
  rw [hA.setBernoulli_real_eq_finiteBernoulliProbability q,
    hA.setBernoulli_real_eq_finiteBernoulliProbability p, hq]
  exact finiteBernoulliProbability_rpow_le hAinc.isIncreasingTrace_eventTrace hp0 hp1 hγ

/-- **Theorem (2.38).** For an increasing event depending on finitely many coordinates, the
ratio `log P_p(A) / log p` is non-increasing on `(0, 1)`: for `0 < p ≤ q < 1`,
`log P_q(A) / log q ≤ log P_p(A) / log p`. Degenerate events (`P ≡ 0`, where both sides
vanish under the `Real.log 0 = 0` convention) are handled via
`finiteBernoulliProbability_eq_zero_of_eq_zero`; no nondegeneracy hypothesis is needed. -/
theorem DependsOn.setBernoulli_real_logRatio_antitone {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (hAinc : IsIncreasingEvent A) {p q : I}
    (hp0 : 0 < (p : ℝ)) (hpq : (p : ℝ) ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    Real.log (setBer((Set.univ : Set ι), q).real A) / Real.log (q : ℝ) ≤
      Real.log (setBer((Set.univ : Set ι), p).real A) / Real.log (p : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := hp0.trans_le hpq
  have hp1 : (p : ℝ) < 1 := hpq.trans_lt hq1
  have hlogq : Real.log (q : ℝ) < 0 := Real.log_neg hq0 hq1
  have hlogp : Real.log (p : ℝ) < 0 := Real.log_neg hp0 hp1
  set γ : ℝ := Real.log (p : ℝ) / Real.log (q : ℝ) with hγdef
  have hγ : 1 ≤ γ := (one_le_div_of_neg hlogq).mpr (Real.log_le_log hp0 hpq)
  have hqγ : (q : ℝ) ^ γ = (p : ℝ) := by
    rw [Real.rpow_def_of_pos hq0, hγdef, mul_comm, div_mul_cancel₀ _ hlogq.ne]
    exact Real.exp_log hp0
  have hfin := finiteBernoulliProbability_rpow_le (E := E)
    hAinc.isIncreasingTrace_eventTrace hq0 hq1 hγ
  rw [hqγ] at hfin
  rw [hA.setBernoulli_real_eq_finiteBernoulliProbability p,
    hA.setBernoulli_real_eq_finiteBernoulliProbability q]
  rcases (finiteBernoulliProbability_nonneg hq0.le hq1.le (eventTrace A)).eq_or_lt with
    hq0' | hqpos
  · have hPp0 : finiteBernoulliProbability E (p : ℝ) (eventTrace A) = 0 := by
      have hzero : finiteBernoulliProbability E (q : ℝ) (eventTrace A) ^ γ = 0 := by
        rw [← hq0', Real.zero_rpow (one_pos.trans_le hγ).ne']
      exact le_antisymm (hfin.trans_eq hzero)
        (finiteBernoulliProbability_nonneg hp0.le hp1.le (eventTrace A))
    rw [hPp0, ← hq0', Real.log_zero, zero_div, zero_div]
  · have hPp0 : 0 < finiteBernoulliProbability E (p : ℝ) (eventTrace A) := by
      rcases (finiteBernoulliProbability_nonneg hp0.le hp1.le (eventTrace A)).eq_or_lt with
        h0 | hpos
      · exact absurd (finiteBernoulliProbability_eq_zero_of_eq_zero hp0 hp1 h0.symm (q : ℝ))
          hqpos.ne'
      · exact hpos
    have hlog : Real.log (finiteBernoulliProbability E (p : ℝ) (eventTrace A)) ≤
        γ * Real.log (finiteBernoulliProbability E (q : ℝ) (eventTrace A)) := by
      have h := Real.log_le_log hPp0 hfin
      rwa [Real.log_rpow hqpos] at h
    rw [le_div_iff_of_neg hlogp]
    calc Real.log (finiteBernoulliProbability E (p : ℝ) (eventTrace A))
        ≤ γ * Real.log (finiteBernoulliProbability E (q : ℝ) (eventTrace A)) := hlog
      _ = Real.log (finiteBernoulliProbability E (q : ℝ) (eventTrace A)) /
            Real.log (q : ℝ) * Real.log (p : ℝ) := by
          rw [hγdef]; ring

/-- Theorem (2.38) for the cubic-lattice Bernoulli bond measure. -/
theorem DependsOn.bernoulliBondMeasure_real_logRatio_antitone {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (hAinc : IsIncreasingEvent A) {p q : I}
    (hp0 : 0 < (p : ℝ)) (hpq : (p : ℝ) ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) :
    Real.log ((bernoulliBondMeasure d q).real A) / Real.log (q : ℝ) ≤
      Real.log ((bernoulliBondMeasure d p).real A) / Real.log (p : ℝ) := by
  simpa [bernoulliBondMeasure] using
    hA.setBernoulli_real_logRatio_antitone hAinc hp0 hpq hq1

end Percolation
