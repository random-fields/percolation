import Percolation.Critical.AdaptiveQueryDomination

/-!
# Ratio-free comparison for adaptive decision trees

Chronological survival is not generally a coordinatewise increasing function of chronological
answer bits: accepting an extra branch may change which vertex is queried by a later bit.  The
appropriate comparison is instead dynamic programming on the exploration tree.  If, at every
history, the iid continuation value after a successful next answer is at least the continuation
value after failure, then uniform ratio-free next-success estimates compare the entire adaptive
tree with its iid counterpart.

This theorem is the probability kernel required by the faithful version of Grimmett Lemma 7.24.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory

namespace AdaptiveSiteExploration

variable {V Omega : Type*}

open Classical

theorem sum_boolVector_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ bits, f bits =
      ∑ b : Bool, ∑ tail : Fin n → Bool, f (Fin.cons b tail) := by
  calc
    ∑ bits, f bits =
        ∑ z : Bool × (Fin n → Bool), f ((Fin.consEquiv fun _ ↦ Bool) z) :=
      (Equiv.sum_comp (Fin.consEquiv fun _ ↦ Bool) f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      rfl

theorem list_ofFn_cons {n : ℕ} (b : Bool) (bits : Fin n → Bool) :
    List.ofFn (Fin.cons b bits) = b :: List.ofFn bits := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Iid Bernoulli probability of winning after exactly `depth` further adaptive queries. -/
noncomputable def iidAdaptiveDecisionValue
    (q : ℝ) (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop) :
    List (V × Bool) → ℕ → ℝ
  | history, 0 => if win history then 1 else 0
  | history, depth + 1 =>
      q * iidAdaptiveDecisionValue q query win
          (history ++ [(query history, true)]) depth +
        (1 - q) * iidAdaptiveDecisionValue q query win
          (history ++ [(query history, false)]) depth

/-- Total mass of exact adaptive histories which win after `depth` further queries. -/
noncomputable def adaptiveDecisionWinMass
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop)
    (history : List (V × Bool)) (depth : ℕ) : ℝ :=
  ∑ bits : Fin depth → Bool,
    if win (adaptiveQueryHistoryFrom query history (List.ofFn bits)) then
      mu.real (adaptiveAnswerHistoryEvent answer
        (adaptiveQueryHistoryFrom query history (List.ofFn bits)))
    else 0

theorem adaptiveDecisionWinMass_zero
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop)
    (history : List (V × Bool)) :
    adaptiveDecisionWinMass mu answer query win history 0 =
      if win history then
        mu.real (adaptiveAnswerHistoryEvent answer history)
      else 0 := by
  simp [adaptiveDecisionWinMass]

theorem adaptiveDecisionWinMass_succ
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop)
    (history : List (V × Bool)) (depth : ℕ) :
    adaptiveDecisionWinMass mu answer query win history (depth + 1) =
      adaptiveDecisionWinMass mu answer query win
          (history ++ [(query history, true)]) depth +
        adaptiveDecisionWinMass mu answer query win
          (history ++ [(query history, false)]) depth := by
  rw [adaptiveDecisionWinMass, sum_boolVector_cons, Fintype.sum_bool]
  simp only [list_ofFn_cons, adaptiveQueryHistoryFrom]
  rfl

/-- The iid continuation value favors a successful answer at every decision-tree node. -/
def IsSuccessFavorable
    (q : ℝ) (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop) : Prop :=
  ∀ history depth,
    iidAdaptiveDecisionValue q query win
        (history ++ [(query history, false)]) depth ≤
      iidAdaptiveDecisionValue q query win
        (history ++ [(query history, true)]) depth

theorem iidAdaptiveDecisionValue_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop) :
    ∀ history depth, 0 ≤ iidAdaptiveDecisionValue q query win history depth := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      by_cases hwin : win history <;> simp [iidAdaptiveDecisionValue, hwin]
  | succ depth ih =>
      rw [iidAdaptiveDecisionValue]
      exact add_nonneg (mul_nonneg hq0 (ih _))
        (mul_nonneg (sub_nonneg.mpr hq1) (ih _))

/-- Dynamic-programming comparison of the iid and history-dependent decision trees.  The theorem
is ratio-free at every node and therefore includes zero-mass histories without division. -/
theorem iidAdaptiveDecisionValue_mul_historyMass_le
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlower : HasAdaptiveAnswerLowerBoundOn mu answer admissible q)
    (hquery : ∀ history, admissible history (query history))
    (win : List (V × Bool) → Prop)
    (hfavorable : IsSuccessFavorable q query win) :
    ∀ history depth,
      iidAdaptiveDecisionValue q query win history depth *
          mu.real (adaptiveAnswerHistoryEvent answer history) ≤
        adaptiveDecisionWinMass mu answer query win history depth := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      rw [iidAdaptiveDecisionValue, adaptiveDecisionWinMass_zero]
      split <;> simp
  | succ depth ih =>
      let v := query history
      let historyTrue := history ++ [(v, true)]
      let historyFalse := history ++ [(v, false)]
      let valueTrue := iidAdaptiveDecisionValue q query win historyTrue depth
      let valueFalse := iidAdaptiveDecisionValue q query win historyFalse depth
      let massHistory := mu.real (adaptiveAnswerHistoryEvent answer history)
      let massTrue := mu.real (adaptiveAnswerHistoryEvent answer historyTrue)
      let massFalse := mu.real (adaptiveAnswerHistoryEvent answer historyFalse)
      have hvalueTrue0 : 0 ≤ valueTrue :=
        iidAdaptiveDecisionValue_nonneg hq0 hq1 query win historyTrue depth
      have hvalueFalse0 : 0 ≤ valueFalse :=
        iidAdaptiveDecisionValue_nonneg hq0 hq1 query win historyFalse depth
      have hvalue : valueFalse ≤ valueTrue := hfavorable history depth
      have hmassPartition : massTrue + massFalse = massHistory := by
        exact measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
          mu hanswer history v
      have hmassTrue : q * massHistory ≤ massTrue := by
        exact hlower history v (hquery history)
      have hbranches :
          valueTrue * massTrue + valueFalse * massFalse ≤
            adaptiveDecisionWinMass mu answer query win historyTrue depth +
              adaptiveDecisionWinMass mu answer query win historyFalse depth :=
        by exact add_le_add (ih historyTrue) (ih historyFalse)
      rw [iidAdaptiveDecisionValue, adaptiveDecisionWinMass_succ]
      dsimp [v, historyTrue, historyFalse, valueTrue, valueFalse,
        massHistory, massTrue, massFalse] at *
      calc
        (q * valueTrue + (1 - q) * valueFalse) * massHistory ≤
            valueTrue * massTrue + valueFalse * massFalse := by
          nlinarith
        _ ≤ _ := hbranches

/-- Dual dynamic-programming comparison.  A ratio-free upper bound on every next success makes
the history-dependent adaptive tree no more likely to win than the iid tree, provided success
is favorable for the continuation value. -/
theorem adaptiveDecisionWinMass_le_iidAdaptiveDecisionValue_mul_historyMass
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hupper : HasAdaptiveAnswerUpperBoundOn mu answer admissible q)
    (hquery : ∀ history, admissible history (query history))
    (win : List (V × Bool) → Prop)
    (hfavorable : IsSuccessFavorable q query win) :
    ∀ history depth,
      adaptiveDecisionWinMass mu answer query win history depth ≤
        iidAdaptiveDecisionValue q query win history depth *
          mu.real (adaptiveAnswerHistoryEvent answer history) := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      rw [iidAdaptiveDecisionValue, adaptiveDecisionWinMass_zero]
      split <;> simp
  | succ depth ih =>
      let v := query history
      let historyTrue := history ++ [(v, true)]
      let historyFalse := history ++ [(v, false)]
      let valueTrue := iidAdaptiveDecisionValue q query win historyTrue depth
      let valueFalse := iidAdaptiveDecisionValue q query win historyFalse depth
      let massHistory := mu.real (adaptiveAnswerHistoryEvent answer history)
      let massTrue := mu.real (adaptiveAnswerHistoryEvent answer historyTrue)
      let massFalse := mu.real (adaptiveAnswerHistoryEvent answer historyFalse)
      have hvalueTrue0 : 0 ≤ valueTrue :=
        iidAdaptiveDecisionValue_nonneg hq0 hq1 query win historyTrue depth
      have hvalueFalse0 : 0 ≤ valueFalse :=
        iidAdaptiveDecisionValue_nonneg hq0 hq1 query win historyFalse depth
      have hvalue : valueFalse ≤ valueTrue := hfavorable history depth
      have hmassHistory0 : 0 ≤ massHistory := measureReal_nonneg
      have hmassTrue0 : 0 ≤ massTrue := measureReal_nonneg
      have hmassFalse0 : 0 ≤ massFalse := measureReal_nonneg
      have hmassPartition : massTrue + massFalse = massHistory := by
        exact measureReal_adaptiveAnswerHistoryEvent_append_true_add_false
          mu hanswer history v
      have hmassTrue : massTrue ≤ q * massHistory := by
        exact hupper history v (hquery history)
      have hbranches :
          adaptiveDecisionWinMass mu answer query win historyTrue depth +
              adaptiveDecisionWinMass mu answer query win historyFalse depth ≤
            valueTrue * massTrue + valueFalse * massFalse :=
        add_le_add (ih historyTrue) (ih historyFalse)
      rw [iidAdaptiveDecisionValue, adaptiveDecisionWinMass_succ]
      dsimp [v, historyTrue, historyFalse, valueTrue, valueFalse,
        massHistory, massTrue, massFalse] at *
      calc
        _ ≤ valueTrue * massTrue + valueFalse * massFalse := hbranches
        _ ≤ (q * valueTrue + (1 - q) * valueFalse) * massHistory := by
          nlinarith

/-- Exact adaptive Bernoulli kernels reproduce the iid decision-tree value for every winning
predicate.  Unlike the one-sided comparison theorems, no continuation monotonicity premise is
needed: both branches have their exact iid masses. -/
theorem adaptiveDecisionWinMass_eq_iidAdaptiveDecisionValue_mul_historyMass
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ)
    (hexact : HasAdaptiveAnswerExactOn mu answer admissible q)
    (hquery : ∀ history, admissible history (query history))
    (win : List (V × Bool) → Prop) :
    ∀ history depth,
      adaptiveDecisionWinMass mu answer query win history depth =
        iidAdaptiveDecisionValue q query win history depth *
          mu.real (adaptiveAnswerHistoryEvent answer history) := by
  intro history depth
  induction depth generalizing history with
  | zero =>
      rw [iidAdaptiveDecisionValue, adaptiveDecisionWinMass_zero]
      split <;> simp
  | succ depth ih =>
      let v := query history
      let historyTrue := history ++ [(v, true)]
      let historyFalse := history ++ [(v, false)]
      let valueTrue := iidAdaptiveDecisionValue q query win historyTrue depth
      let valueFalse := iidAdaptiveDecisionValue q query win historyFalse depth
      let massHistory := mu.real (adaptiveAnswerHistoryEvent answer history)
      let massTrue := mu.real (adaptiveAnswerHistoryEvent answer historyTrue)
      let massFalse := mu.real (adaptiveAnswerHistoryEvent answer historyFalse)
      have hmassTrue : massTrue = q * massHistory := by
        exact hexact history v (hquery history)
      have hmassFalse : massFalse = (1 - q) * massHistory := by
        exact hexact.false_mass_eq hanswer (hquery history)
      rw [iidAdaptiveDecisionValue, adaptiveDecisionWinMass_succ, ih, ih]
      dsimp [v, historyTrue, historyFalse, valueTrue, valueFalse,
        massHistory, massTrue, massFalse] at *
      rw [hmassTrue, hmassFalse]
      ring

/-- Root form of the exact adaptive-tree identity under a probability measure. -/
theorem winMass_eq_iidAdaptiveDecisionValue
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ)
    (hexact : HasAdaptiveAnswerExactOn mu answer admissible q)
    (hquery : ∀ history, admissible history (query history))
    (win : List (V × Bool) → Prop) (depth : ℕ) :
    adaptiveDecisionWinMass mu answer query win [] depth =
      iidAdaptiveDecisionValue q query win [] depth := by
  simpa [probReal_univ] using
    adaptiveDecisionWinMass_eq_iidAdaptiveDecisionValue_mul_historyMass
      mu hanswer query admissible q hexact hquery win [] depth

/-- Exact Bernoulli extensions only along the histories actually generated by `query` identify
the winning mass with the explicit iid Boolean leaf sum.  Malformed histories need no law. -/
theorem adaptiveDecisionWinMass_eq_sum_iidBoolWeight_of_exactAlong
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V) (q : ℝ)
    (hexact : ∀ bits : List Bool,
      mu.real (adaptiveAnswerHistoryEvent answer
          (adaptiveQueryHistory query bits ++
            [(query (adaptiveQueryHistory query bits), true)])) =
        q * mu.real (adaptiveAnswerHistoryEvent answer
          (adaptiveQueryHistory query bits)))
    (win : List (V × Bool) → Prop) (depth : ℕ) :
    adaptiveDecisionWinMass mu answer query win [] depth =
      ∑ bits : Fin depth → Bool,
        if win (adaptiveQueryHistory query (List.ofFn bits)) then
          iidBoolWeight depth q bits else 0 := by
  rw [adaptiveDecisionWinMass]
  apply Finset.sum_congr rfl
  intro bits _hbits
  change (if win (adaptiveQueryHistory query (List.ofFn bits)) then
      adaptiveQueryWeight mu answer query depth bits else 0) =
    (if win (adaptiveQueryHistory query (List.ofFn bits)) then
      iidBoolWeight depth q bits else 0)
  by_cases hwin : win (adaptiveQueryHistory query (List.ofFn bits))
  · rw [if_pos hwin, if_pos hwin]
    exact adaptiveQueryWeight_eq_iidBoolWeight_of_exactAlong
      mu hanswer query q hexact depth bits
  · rw [if_neg hwin, if_neg hwin]

/-- Root form under a probability measure. -/
theorem iidAdaptiveDecisionValue_le_winMass
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlower : HasAdaptiveAnswerLowerBoundOn mu answer admissible q)
    (hquery : ∀ history, admissible history (query history))
    (win : List (V × Bool) → Prop)
    (hfavorable : IsSuccessFavorable q query win) (depth : ℕ) :
    iidAdaptiveDecisionValue q query win [] depth ≤
      adaptiveDecisionWinMass mu answer query win [] depth := by
  simpa [probReal_univ] using
    iidAdaptiveDecisionValue_mul_historyMass_le mu hanswer query admissible q hq0 hq1
      hlower hquery win hfavorable [] depth

/-- Root form of the dual adaptive-tree comparison under a probability measure. -/
theorem winMass_le_iidAdaptiveDecisionValue
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (admissible : List (V × Bool) → V → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hupper : HasAdaptiveAnswerUpperBoundOn mu answer admissible q)
    (hquery : ∀ history, admissible history (query history))
    (win : List (V × Bool) → Prop)
    (hfavorable : IsSuccessFavorable q query win) (depth : ℕ) :
    adaptiveDecisionWinMass mu answer query win [] depth ≤
      iidAdaptiveDecisionValue q query win [] depth := by
  simpa [probReal_univ] using
    adaptiveDecisionWinMass_le_iidAdaptiveDecisionValue_mul_historyMass
      mu hanswer query admissible q hq0 hq1 hupper hquery win hfavorable [] depth

end AdaptiveSiteExploration

end Percolation
