import Percolation.Critical.DynamicBlockCertificate

/-!
# Finite composition of block-success estimates

Equations (7.30) and (7.33) combine finitely many ratio-free restart bounds.  These lemmas keep
that bookkeeping explicit: one is the finite union bound for simultaneous branches, and the
other iterates history-dependent conditional lower bounds without dividing by null histories.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Ratio-free finite union bound.  If every branch succeeds on `H` with relative failure less
than `epsilon`, all branches succeed with relative failure less than `card ι * epsilon`. -/
theorem allSuccess_inter_history_gt
    {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota] [Nonempty iota]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (G : iota → Set Omega) (H : Set Omega)
    (hG : ∀ i, MeasurableSet (G i)) (hH : MeasurableSet H)
    (epsilon : ℝ)
    (hsuccess : ∀ i,
      (1 - epsilon) * mu.real H < mu.real (G i ∩ H)) :
    (1 - Fintype.card iota * epsilon) * mu.real H <
      mu.real ((⋂ i, G i) ∩ H) := by
  have hdiffMeasure : ∀ i,
      mu.real (H \ G i) = mu.real H - mu.real (G i ∩ H) := by
    intro i
    have hset : H \ G i = H \ (G i ∩ H) := by
      ext omega
      simp
    rw [hset, measureReal_diff Set.inter_subset_right ((hG i).inter hH)]
  have hfailure : ∀ i, mu.real (H \ G i) < epsilon * mu.real H := by
    intro i
    rw [hdiffMeasure]
    nlinarith [hsuccess i]
  have hdiffSet : H \ ((⋂ i, G i) ∩ H) = ⋃ i, H \ G i := by
    ext omega
    simp
  have hfailureAll :
      mu.real (H \ ((⋂ i, G i) ∩ H)) <
        Fintype.card iota * (epsilon * mu.real H) := by
    rw [hdiffSet]
    calc
      mu.real (⋃ i, H \ G i) ≤ ∑ i, mu.real (H \ G i) :=
        measureReal_iUnion_fintype_le _
      _ < ∑ _i : iota, epsilon * mu.real H :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ hfailure i
      _ = Fintype.card iota * (epsilon * mu.real H) := by
        simp [nsmul_eq_mul]
  have hInterMeas : MeasurableSet ((⋂ i, G i) ∩ H) :=
    (MeasurableSet.iInter hG).inter hH
  have hdiffEq :
      mu.real (H \ ((⋂ i, G i) ∩ H)) =
        mu.real H - mu.real ((⋂ i, G i) ∩ H) :=
    measureReal_diff Set.inter_subset_right hInterMeas
  rw [hdiffEq] at hfailureAll
  nlinarith

/-- Iteration of ratio-free conditional lower bounds along an adaptive finite history. -/
theorem pow_mul_measureReal_le_of_step
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (history : ℕ → Set Omega) (a : ℝ) (ha : 0 ≤ a) (k : ℕ)
    (hstep : ∀ j < k,
      a * mu.real (history j) ≤ mu.real (history (j + 1))) :
    a ^ k * mu.real (history 0) ≤ mu.real (history k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        a ^ (k + 1) * mu.real (history 0) =
            a * (a ^ k * mu.real (history 0)) := by ring
        _ ≤ a * mu.real (history k) :=
          mul_le_mul_of_nonneg_left
            (ih fun j hj ↦ hstep j (by omega)) ha
        _ ≤ mu.real (history (k + 1)) := hstep k (by omega)

/-- Strict version used when every positive-mass restart estimate is strict. -/
theorem pow_mul_measureReal_lt_of_step
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (history : ℕ → Set Omega) (a : ℝ) (ha : 0 < a) (k : ℕ) (hk : 0 < k)
    (hstep : ∀ j < k,
      a * mu.real (history j) < mu.real (history (j + 1))) :
    a ^ k * mu.real (history 0) < mu.real (history k) := by
  induction k with
  | zero => simp at hk
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa using hstep 0 (by omega)
      · calc
          a ^ (k + 1) * mu.real (history 0) =
              a * (a ^ k * mu.real (history 0)) := by ring
          _ < a * mu.real (history k) := by
            exact mul_lt_mul_of_pos_left
              (ih (by omega) (fun j hj ↦ hstep j (by omega))) ha
          _ < mu.real (history (k + 1)) := hstep k (by omega)

/-- A ratio-free restart bound remains valid after intersecting with an independent piece of
the earlier exploration history.  Both independence hypotheses are explicit: the past must be
independent of the boundary cell itself and of the successful part of that cell.  This is the
finite-support factorization used when a fresh oriented restart is appended to a dynamic block
history. -/
theorem mul_measureReal_inter_le_inter_of_indepSet
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {past history success : Set Omega} {q : ℝ}
    (hpastHistory : IndepSet past history mu)
    (hpastSuccessHistory : IndepSet past (success ∩ history) mu)
    (hlower : q * mu.real history ≤ mu.real (success ∩ history)) :
    q * mu.real (past ∩ history) ≤
      mu.real (success ∩ (past ∩ history)) := by
  have hPastHistory :
      mu.real (past ∩ history) = mu.real past * mu.real history := by
    have h := congrArg ENNReal.toReal hpastHistory.measure_inter_eq_mul
    simpa [Measure.real, ENNReal.toReal_mul] using h
  have hPastSuccessHistory :
      mu.real (past ∩ (success ∩ history)) =
        mu.real past * mu.real (success ∩ history) := by
    have h := congrArg ENNReal.toReal hpastSuccessHistory.measure_inter_eq_mul
    simpa [Measure.real, ENNReal.toReal_mul] using h
  rw [hPastHistory]
  calc
    q * (mu.real past * mu.real history) =
        mu.real past * (q * mu.real history) := by ring
    _ ≤ mu.real past * mu.real (success ∩ history) :=
      mul_le_mul_of_nonneg_left hlower (measureReal_nonneg)
    _ = mu.real (past ∩ (success ∩ history)) := hPastSuccessHistory.symm
    _ = mu.real (success ∩ (past ∩ history)) := by
      congr 1
      ext omega
      simp only [Set.mem_inter_iff]
      tauto

/-- Strict form of `mul_measureReal_inter_le_inter_of_indepSet`.  Positivity of the past cell is
necessary and is stated rather than silently inferred from a conditional-probability notation. -/
theorem mul_measureReal_inter_lt_inter_of_indepSet
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {past history success : Set Omega} {q : ℝ}
    (hpastHistory : IndepSet past history mu)
    (hpastSuccessHistory : IndepSet past (success ∩ history) mu)
    (hpast : 0 < mu.real past)
    (hlower : q * mu.real history < mu.real (success ∩ history)) :
    q * mu.real (past ∩ history) <
      mu.real (success ∩ (past ∩ history)) := by
  have hPastHistory :
      mu.real (past ∩ history) = mu.real past * mu.real history := by
    have h := congrArg ENNReal.toReal hpastHistory.measure_inter_eq_mul
    simpa [Measure.real, ENNReal.toReal_mul] using h
  have hPastSuccessHistory :
      mu.real (past ∩ (success ∩ history)) =
        mu.real past * mu.real (success ∩ history) := by
    have h := congrArg ENNReal.toReal hpastSuccessHistory.measure_inter_eq_mul
    simpa [Measure.real, ENNReal.toReal_mul] using h
  rw [hPastHistory]
  calc
    q * (mu.real past * mu.real history) =
        mu.real past * (q * mu.real history) := by ring
    _ < mu.real past * mu.real (success ∩ history) :=
      mul_lt_mul_of_pos_left hlower hpast
    _ = mu.real (past ∩ (success ∩ history)) := hPastSuccessHistory.symm
    _ = mu.real (success ∩ (past ∩ history)) := by
      congr 1
      ext omega
      simp only [Set.mem_inter_iff]
      tauto

end Percolation
