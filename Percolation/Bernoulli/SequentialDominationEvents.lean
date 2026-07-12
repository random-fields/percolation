import Percolation.Bernoulli.LSSDilution
import Percolation.Bernoulli.SequentialDomination

/-!
# Event form of finite sequential domination

The finite comparison theorem is implemented using atomic Boolean masses.  Conditional
arguments such as Grimmett (7.117) are more naturally stated as inequalities between exact
prefix events.  This file proves the two presentations identical, retaining the ratio-free form
on null histories.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory

/-- Configurations whose first `i` Boolean coordinates equal `s`. -/
def finiteBoolPrefixEvent {n i : ℕ} (hi : i ≤ n)
    (s : Fin i → Bool) : Set (Set (Fin n)) :=
  {ω | boolPrefix hi (finiteSetBoolEquiv n ω) = s}

/-- Exact prefix event with the next coordinate open. -/
def finiteBoolPrefixOpenEvent {n i : ℕ} (hi : i < n)
    (s : Fin i → Bool) : Set (Set (Fin n)) :=
  finiteBoolPrefixEvent hi.le s ∩ {ω | ⟨i, hi⟩ ∈ ω}

theorem measurableSet_finiteBoolPrefixEvent {n i : ℕ}
    (hi : i ≤ n) (s : Fin i → Bool) :
    MeasurableSet (finiteBoolPrefixEvent hi s) :=
  Set.toFinite _ |>.measurableSet

theorem measurableSet_finiteBoolPrefixOpenEvent {n i : ℕ}
    (hi : i < n) (s : Fin i → Bool) :
    MeasurableSet (finiteBoolPrefixOpenEvent hi s) :=
  Set.toFinite _ |>.measurableSet

theorem measureReal_finiteBoolPrefixEvent_eq_boolPrefixMass
    {n i : ℕ} (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu]
    (hi : i ≤ n) (s : Fin i → Bool) :
    mu.real (finiteBoolPrefixEvent hi s) =
      boolPrefixMass (finiteSetBoolMass mu) hi s := by
  rw [measureReal_eq_sum_indicator_singleton]
  let e := (finiteSetBoolEquiv n).symm
  let f : Set (Fin n) → ℝ := fun ω =>
    (finiteBoolPrefixEvent hi s).indicator (fun ξ => mu.real {ξ}) ω
  have hsum := Equiv.sum_comp e f
  rw [boolPrefixMass]
  simpa [finiteBoolPrefixEvent, finiteSetBoolMass, e, f, Set.indicator, apply_ite]
    using hsum.symm

theorem measureReal_finiteBoolPrefixOpenEvent_eq_boolPrefixOpenMass
    {n i : ℕ} (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu]
    (hi : i < n) (s : Fin i → Bool) :
    mu.real (finiteBoolPrefixOpenEvent hi s) =
      boolPrefixOpenMass (finiteSetBoolMass mu) hi s := by
  rw [measureReal_eq_sum_indicator_singleton]
  let e := (finiteSetBoolEquiv n).symm
  let f : Set (Fin n) → ℝ := fun ω =>
    (finiteBoolPrefixOpenEvent hi s).indicator (fun ξ => mu.real {ξ}) ω
  have hsum := Equiv.sum_comp e f
  rw [boolPrefixOpenMass]
  simpa [finiteBoolPrefixOpenEvent, finiteBoolPrefixEvent, finiteSetBoolMass,
    e, f, Set.indicator, apply_ite] using hsum.symm

/-- Exact event-mass characterization of the finite ratio-free sequential premise. -/
theorem hasFiniteSequentialLowerBound_iff_event
    {n : ℕ} (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu] (p : ℝ) :
    HasFiniteSequentialLowerBound mu p ↔
      ∀ i (hi : i < n) (s : Fin i → Bool),
        p * mu.real (finiteBoolPrefixEvent hi.le s) ≤
          mu.real (finiteBoolPrefixOpenEvent hi s) := by
  unfold HasFiniteSequentialLowerBound HasSequentialLowerBound
  constructor <;> intro h i hi s
  · simpa only [measureReal_finiteBoolPrefixEvent_eq_boolPrefixMass,
      measureReal_finiteBoolPrefixOpenEvent_eq_boolPrefixOpenMass] using h i hi s
  · simpa only [measureReal_finiteBoolPrefixEvent_eq_boolPrefixMass,
      measureReal_finiteBoolPrefixOpenEvent_eq_boolPrefixOpenMass] using h i hi s

end Percolation
