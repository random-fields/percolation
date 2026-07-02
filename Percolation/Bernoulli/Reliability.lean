import Percolation.Bernoulli.Russo

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
