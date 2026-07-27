import Percolation.Bernoulli.FiniteCube
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# The FKG inequality on finite supports

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.2, Theorem (2.4) and corollary (2.7),
pp. 34–36 (source id `grimmett-percolation-1999`), restricted to events and observables
depending on finitely many edges. The general (infinite-support) version follows in
`Percolation.Bernoulli.FKGInfinite` by martingale approximation, exactly as in the book.

The finite core is obtained by bridging to Mathlib's Ahlswede–Daykin four functions theorem
`Finset.four_functions_theorem` on the powerset algebra: the Bernoulli weight
`p^{|s|}(1-p)^{|E|-|s|}` is log-supermodular *with equality*
(`finiteBernoulliWeight_mul_weight`, from `|s ∩ t| + |s ∪ t| = |s| + |t|`), which yields FKG
for nonnegative monotone observables; a constant shift removes the sign hypothesis, and
indicators specialize to events. This is a recorded divergence from Grimmett's proof by
induction on the number of coordinates; the statements are unchanged.

Main results:

* `Percolation.finiteBernoulliExpectation_mul_fkg_of_monotone` — Theorem 2.4(a) on the
  finite cube: `E_p(X) E_p(Y) ≤ E_p(XY)` for monotone `X`, `Y`;
* `Percolation.finiteBernoulliProbability_fkg` — Theorem 2.4(b) on the finite cube;
* `Percolation.setBernoulli_real_fkg_of_dependsOn` and variants — Theorem 2.4(b) for
  finitely supported increasing/decreasing events of the ambient product measure, with the
  mixed-monotonicity reversal and the iterated corollary (2.7);
* `Percolation.setBernoulli_integral_fkg_of_dependsOnFun` — Theorem 2.4(a) for finitely
  supported increasing observables;
* `bernoulliBondMeasure_*` specializations to the cubic lattice.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Finset unitInterval FinsetFamily

variable {ι : Type*}

/-- A trace event is decreasing when it is downward closed for finite-set inclusion. -/
def IsDecreasingTrace (T : Set (Finset ι)) : Prop :=
  ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ∈ T → s ∈ T

theorem IsDecreasingEvent.isDecreasingTrace_eventTrace {A : Set (Set ι)}
    (hA : IsDecreasingEvent A) : IsDecreasingTrace (eventTrace A) :=
  fun _ _ hst ht => hA (Finset.coe_subset.mpr hst) ht

/-- The Bernoulli weight is log-supermodular with equality: opening patterns recombine
across intersections and unions without loss (`|s ∩ t| + |s ∪ t| = |s| + |t|`). -/
theorem finiteBernoulliWeight_mul_weight [DecidableEq ι] {E : Finset ι} (p : ℝ)
    {s t : Finset ι} (hs : s ⊆ E) (ht : t ⊆ E) :
    finiteBernoulliWeight E p s * finiteBernoulliWeight E p t =
      finiteBernoulliWeight E p (s ∩ t) * finiteBernoulliWeight E p (s ∪ t) := by
  have hcard : (s ∩ t).card + (s ∪ t).card = s.card + t.card :=
    Finset.card_inter_add_card_union s t
  have hsE : s.card ≤ E.card := Finset.card_le_card hs
  have htE : t.card ≤ E.card := Finset.card_le_card ht
  have hiE : (s ∩ t).card ≤ E.card :=
    Finset.card_le_card ((Finset.inter_subset_left).trans hs)
  have huE : (s ∪ t).card ≤ E.card := Finset.card_le_card (Finset.union_subset hs ht)
  rw [finiteBernoulliWeight, finiteBernoulliWeight, finiteBernoulliWeight,
    finiteBernoulliWeight]
  rw [show p ^ s.card * (1 - p) ^ (E.card - s.card) * (p ^ t.card * (1 - p) ^ (E.card - t.card)) =
      p ^ (s.card + t.card) * (1 - p) ^ ((E.card - s.card) + (E.card - t.card)) by
    rw [pow_add, pow_add]; ring]
  rw [show p ^ (s ∩ t).card * (1 - p) ^ (E.card - (s ∩ t).card) *
        (p ^ (s ∪ t).card * (1 - p) ^ (E.card - (s ∪ t).card)) =
      p ^ ((s ∩ t).card + (s ∪ t).card) *
        (1 - p) ^ ((E.card - (s ∩ t).card) + (E.card - (s ∪ t).card)) by
    rw [pow_add, pow_add]; ring]
  have h1 : (s ∩ t).card + (s ∪ t).card = s.card + t.card := hcard
  have h2 : (E.card - (s ∩ t).card) + (E.card - (s ∪ t).card) =
      (E.card - s.card) + (E.card - t.card) := by omega
  rw [h1, h2]

/-- **FKG inequality, finite nonnegative core** (Grimmett Theorem (2.4a) on the finite
cube, nonnegative monotone observables), by the Ahlswede–Daykin four functions theorem. -/
theorem finiteBernoulliExpectation_mul_fkg {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : Finset ι → ℝ}
    (hf0 : ∀ s ⊆ E, 0 ≤ f s) (hg0 : ∀ s ⊆ E, 0 ≤ g s)
    (hf : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → f s ≤ f t)
    (hg : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → g s ≤ g t) :
    finiteBernoulliExpectation E p f * finiteBernoulliExpectation E p g ≤
      finiteBernoulliExpectation E p (fun s => f s * g s) := by
  classical
  set w : Finset ι → ℝ := finiteBernoulliWeight E p with hw
  set f₁ : Finset ι → ℝ := fun s => if s ⊆ E then w s * f s else 0 with hf₁
  set f₂ : Finset ι → ℝ := fun s => if s ⊆ E then w s * g s else 0 with hf₂
  set f₃ : Finset ι → ℝ := fun s => if s ⊆ E then w s else 0 with hf₃
  set f₄ : Finset ι → ℝ := fun s => if s ⊆ E then w s * (f s * g s) else 0 with hf₄
  have hw0 : ∀ s : Finset ι, 0 ≤ w s := finiteBernoulliWeight_nonneg hp0 hp1
  have h₁ : 0 ≤ f₁ := by
    intro s
    by_cases hs : s ⊆ E
    · simpa [hf₁, hs] using mul_nonneg (hw0 s) (hf0 s hs)
    · simp [hf₁, hs]
  have h₂ : 0 ≤ f₂ := by
    intro s
    by_cases hs : s ⊆ E
    · simpa [hf₂, hs] using mul_nonneg (hw0 s) (hg0 s hs)
    · simp [hf₂, hs]
  have h₃ : 0 ≤ f₃ := by
    intro s
    by_cases hs : s ⊆ E
    · simpa [hf₃, hs] using hw0 s
    · simp [hf₃, hs]
  have h₄ : 0 ≤ f₄ := by
    intro s
    by_cases hs : s ⊆ E
    · simpa [hf₄, hs] using
        mul_nonneg (hw0 s) (mul_nonneg (hf0 s hs) (hg0 s hs))
    · simp [hf₄, hs]
  have hkey : ∀ ⦃s : Finset ι⦄, s ⊆ E → ∀ ⦃t : Finset ι⦄, t ⊆ E →
      f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t) := by
    intro s hs t ht
    have hst : s ∩ t ⊆ E := Finset.inter_subset_left.trans hs
    have hut : s ∪ t ⊆ E := Finset.union_subset hs ht
    rw [hf₁, hf₂, hf₃, hf₄]
    simp only [hs, ht, hst, hut, if_true]
    calc w s * f s * (w t * g t)
        = (w s * w t) * (f s * g t) := by ring
      _ = (w (s ∩ t) * w (s ∪ t)) * (f s * g t) := by
          rw [finiteBernoulliWeight_mul_weight p hs ht]
      _ ≤ (w (s ∩ t) * w (s ∪ t)) * (f (s ∪ t) * g (s ∪ t)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (hw0 _) (hw0 _))
          exact mul_le_mul (hf Finset.subset_union_left hut)
            (hg Finset.subset_union_right hut) (hg0 t ht) (hf0 _ hut)
      _ = w (s ∩ t) * (w (s ∪ t) * (f (s ∪ t) * g (s ∪ t))) := by ring
  have h := Finset.four_functions_theorem E h₁ h₂ h₃ h₄ hkey
    (Finset.Subset.refl E.powerset) (Finset.Subset.refl E.powerset)
  rw [Finset.powerset_infs_powerset_self, Finset.powerset_sups_powerset_self] at h
  have e₁ : ∑ s ∈ E.powerset, f₁ s = finiteBernoulliExpectation E p f :=
    Finset.sum_congr rfl fun s hs => by
      simp [hf₁, hw, Finset.mem_powerset.mp hs]
  have e₂ : ∑ s ∈ E.powerset, f₂ s = finiteBernoulliExpectation E p g :=
    Finset.sum_congr rfl fun s hs => by
      simp [hf₂, hw, Finset.mem_powerset.mp hs]
  have e₃ : ∑ s ∈ E.powerset, f₃ s = 1 := by
    rw [show ∑ s ∈ E.powerset, f₃ s = ∑ s ∈ E.powerset, finiteBernoulliWeight E p s from
      Finset.sum_congr rfl fun s hs => by simp [hf₃, hw, Finset.mem_powerset.mp hs]]
    exact sum_finiteBernoulliWeight E p
  have e₄ : ∑ s ∈ E.powerset, f₄ s =
      finiteBernoulliExpectation E p (fun s => f s * g s) :=
    Finset.sum_congr rfl fun s hs => by
      simp [hf₄, hw, Finset.mem_powerset.mp hs]
  rw [e₁, e₂, e₃, e₄, one_mul] at h
  exact h

/-- Shifting an observable by a constant shifts the finite expectation. -/
theorem finiteBernoulliExpectation_sub_const (E : Finset ι) (p : ℝ) (f : Finset ι → ℝ)
    (c : ℝ) :
    finiteBernoulliExpectation E p (fun s => f s - c) =
      finiteBernoulliExpectation E p f - c := by
  rw [finiteBernoulliExpectation_congr (Y := fun s => f s + (-c) * 1) fun s _ => by ring,
    finiteBernoulliExpectation_add, finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_one]
  ring

/-- Bilinear expansion of the finite expectation of a product of shifted observables. -/
theorem finiteBernoulliExpectation_sub_const_mul (E : Finset ι) (p : ℝ)
    (f g : Finset ι → ℝ) (c d : ℝ) :
    finiteBernoulliExpectation E p (fun s => (f s - c) * (g s - d)) =
      finiteBernoulliExpectation E p (fun s => f s * g s) -
        c * finiteBernoulliExpectation E p g - d * finiteBernoulliExpectation E p f +
        c * d := by
  rw [finiteBernoulliExpectation_congr
      (Y := fun s => f s * g s + (-c) * g s + ((-d) * f s + c * d * 1)) fun s _ => by ring,
    finiteBernoulliExpectation_add, finiteBernoulliExpectation_add,
    finiteBernoulliExpectation_add, finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_const_mul, finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_one]
  ring

/-- **FKG inequality for monotone observables** (Theorem (2.4a) on the finite cube): the
sign hypothesis is removed by shifting by the value at `∅`, which is minimal for a monotone
observable. -/
theorem finiteBernoulliExpectation_mul_fkg_of_monotone {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : Finset ι → ℝ}
    (hf : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → f s ≤ f t)
    (hg : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E → g s ≤ g t) :
    finiteBernoulliExpectation E p f * finiteBernoulliExpectation E p g ≤
      finiteBernoulliExpectation E p (fun s => f s * g s) := by
  have hshift := finiteBernoulliExpectation_mul_fkg hp0 hp1
    (f := fun s => f s - f ∅) (g := fun s => g s - g ∅)
    (fun s hs => sub_nonneg.mpr (hf (Finset.empty_subset s) hs))
    (fun s hs => sub_nonneg.mpr (hg (Finset.empty_subset s) hs))
    (fun s t hst htE => sub_le_sub_right (hf hst htE) _)
    (fun s t hst htE => sub_le_sub_right (hg hst htE) _)
  rw [finiteBernoulliExpectation_sub_const, finiteBernoulliExpectation_sub_const,
    finiteBernoulliExpectation_sub_const_mul] at hshift
  nlinarith [hshift]

/-- **FKG inequality for increasing trace events** (Theorem (2.4b) on the finite cube). -/
theorem finiteBernoulliProbability_fkg {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T U : Set (Finset ι)}
    (hT : IsIncreasingTrace T) (hU : IsIncreasingTrace U) :
    finiteBernoulliProbability E p T * finiteBernoulliProbability E p U ≤
      finiteBernoulliProbability E p (T ∩ U) := by
  have hind : ∀ s : Finset ι,
      (T ∩ U).indicator (fun _ => (1 : ℝ)) s =
        T.indicator (fun _ => (1 : ℝ)) s * U.indicator (fun _ => (1 : ℝ)) s := by
    intro s
    by_cases hsT : s ∈ T <;> by_cases hsU : s ∈ U <;>
      simp [hsT, hsU]
  have hmono : ∀ (V : Set (Finset ι)), IsIncreasingTrace V →
      ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E →
        V.indicator (fun _ => (1 : ℝ)) s ≤ V.indicator (fun _ => (1 : ℝ)) t := by
    intro V hV s t hst _
    by_cases hs : s ∈ V
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hV hst hs)]
    · rw [Set.indicator_of_notMem hs]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have h := finiteBernoulliExpectation_mul_fkg hp0 hp1
    (f := T.indicator fun _ => 1) (g := U.indicator fun _ => 1)
    (fun s _ => Set.indicator_apply_nonneg fun _ => zero_le_one)
    (fun s _ => Set.indicator_apply_nonneg fun _ => zero_le_one)
    (hmono T hT) (hmono U hU)
  rw [finiteBernoulliProbability, finiteBernoulliProbability, finiteBernoulliProbability,
    finiteBernoulliExpectation_congr fun s _ => hind s]
  exact h

/-! ### Measure-level FKG for finitely supported events -/

/-- **The FKG inequality** (Grimmett Theorem (2.4b)) for increasing events depending on
finitely many coordinates. -/
theorem setBernoulli_real_fkg_of_dependsOn (p : I) {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real A * setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  classical
  have hA' : DependsOn (E ∪ F) A := hA.mono Finset.subset_union_left
  have hB' : DependsOn (E ∪ F) B := hB.mono Finset.subset_union_right
  rw [hA'.setBernoulli_real_eq_finiteBernoulliProbability p,
    hB'.setBernoulli_real_eq_finiteBernoulliProbability p,
    (hA'.inter hB').setBernoulli_real_eq_finiteBernoulliProbability p]
  have htrace : eventTrace (A ∩ B) = eventTrace A ∩ eventTrace B := rfl
  rw [htrace]
  exact finiteBernoulliProbability_fkg p.2.1 p.2.2
    hAinc.isIncreasingTrace_eventTrace hBinc.isIncreasingTrace_eventTrace

/-- The finite expectation of a `1 - indicator` observable. -/
theorem finiteBernoulliExpectation_one_sub_indicator (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliExpectation E p (fun s => 1 - T.indicator (fun _ => (1 : ℝ)) s) =
      1 - finiteBernoulliProbability E p T := by
  rw [finiteBernoulliExpectation_congr
      (Y := fun s => (1 : ℝ) + (-1) * T.indicator (fun _ => (1 : ℝ)) s)
      fun s _ => by ring,
    finiteBernoulliExpectation_add, finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_const, finiteBernoulliProbability]
  ring

/-- **FKG for decreasing trace events**: two decreasing events are also positively
correlated (Grimmett p. 34, remark after Theorem (2.4)). -/
theorem finiteBernoulliProbability_fkg_of_decreasing {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T U : Set (Finset ι)}
    (hT : IsDecreasingTrace T) (hU : IsDecreasingTrace U) :
    finiteBernoulliProbability E p T * finiteBernoulliProbability E p U ≤
      finiteBernoulliProbability E p (T ∩ U) := by
  have hmono : ∀ (V : Set (Finset ι)), IsDecreasingTrace V →
      ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E →
        1 - V.indicator (fun _ => (1 : ℝ)) s ≤ 1 - V.indicator (fun _ => (1 : ℝ)) t := by
    intro V hV s t hst _
    refine sub_le_sub_left ?_ 1
    by_cases ht : t ∈ V
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hV hst ht)]
    · rw [Set.indicator_of_notMem ht]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have h := finiteBernoulliExpectation_mul_fkg hp0 hp1
    (f := fun s => 1 - T.indicator (fun _ => 1) s)
    (g := fun s => 1 - U.indicator (fun _ => 1) s)
    (fun s _ => sub_nonneg.mpr (Set.indicator_apply_le' (fun _ => le_refl 1)
      fun _ => zero_le_one))
    (fun s _ => sub_nonneg.mpr (Set.indicator_apply_le' (fun _ => le_refl 1)
      fun _ => zero_le_one))
    (hmono T hT) (hmono U hU)
  have hexpand : ∀ s : Finset ι,
      (1 - T.indicator (fun _ => (1 : ℝ)) s) * (1 - U.indicator (fun _ => (1 : ℝ)) s) =
        (T ∩ U).indicator (fun _ => (1 : ℝ)) s + (-1) * T.indicator (fun _ => (1 : ℝ)) s +
          ((-1) * U.indicator (fun _ => (1 : ℝ)) s + 1) := by
    intro s
    by_cases hsT : s ∈ T <;> by_cases hsU : s ∈ U <;>
      simp [hsT, hsU]
  rw [finiteBernoulliExpectation_congr fun s _ => hexpand s,
    finiteBernoulliExpectation_add, finiteBernoulliExpectation_add,
    finiteBernoulliExpectation_add, finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_const_mul, finiteBernoulliExpectation_const,
    finiteBernoulliExpectation_one_sub_indicator,
    finiteBernoulliExpectation_one_sub_indicator] at h
  have hTU : finiteBernoulliExpectation E p ((T ∩ U).indicator fun _ => 1) =
      finiteBernoulliProbability E p (T ∩ U) := rfl
  rw [hTU] at h
  have hT' : finiteBernoulliExpectation E p (T.indicator fun _ => 1) =
      finiteBernoulliProbability E p T := rfl
  have hU' : finiteBernoulliExpectation E p (U.indicator fun _ => 1) =
      finiteBernoulliProbability E p U := rfl
  rw [hT', hU'] at h
  nlinarith [h]

/-- **Mixed monotonicity reverses FKG**: an increasing and a decreasing trace event are
negatively correlated (Grimmett p. 34). -/
theorem finiteBernoulliProbability_le_mul_of_increasing_decreasing {E : Finset ι} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T U : Set (Finset ι)}
    (hT : IsIncreasingTrace T) (hU : IsDecreasingTrace U) :
    finiteBernoulliProbability E p (T ∩ U) ≤
      finiteBernoulliProbability E p T * finiteBernoulliProbability E p U := by
  have hmonoT : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E →
      T.indicator (fun _ => (1 : ℝ)) s ≤ T.indicator (fun _ => (1 : ℝ)) t := by
    intro s t hst _
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hT hst hs)]
    · rw [Set.indicator_of_notMem hs]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have hmonoU : ∀ ⦃s t : Finset ι⦄, s ⊆ t → t ⊆ E →
      1 - U.indicator (fun _ => (1 : ℝ)) s ≤ 1 - U.indicator (fun _ => (1 : ℝ)) t := by
    intro s t hst _
    refine sub_le_sub_left ?_ 1
    by_cases ht : t ∈ U
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hU hst ht)]
    · rw [Set.indicator_of_notMem ht]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have h := finiteBernoulliExpectation_mul_fkg hp0 hp1
    (f := T.indicator fun _ => 1)
    (g := fun s => 1 - U.indicator (fun _ => 1) s)
    (fun s _ => Set.indicator_apply_nonneg fun _ => zero_le_one)
    (fun s _ => sub_nonneg.mpr (Set.indicator_apply_le' (fun _ => le_refl 1)
      fun _ => zero_le_one))
    hmonoT hmonoU
  have hexpand : ∀ s : Finset ι,
      T.indicator (fun _ => (1 : ℝ)) s * (1 - U.indicator (fun _ => (1 : ℝ)) s) =
        T.indicator (fun _ => (1 : ℝ)) s + (-1) * (T ∩ U).indicator (fun _ => (1 : ℝ)) s := by
    intro s
    by_cases hsT : s ∈ T <;> by_cases hsU : s ∈ U <;>
      simp [hsT, hsU]
  rw [finiteBernoulliExpectation_congr fun s _ => hexpand s,
    finiteBernoulliExpectation_add, finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_one_sub_indicator] at h
  have hT' : finiteBernoulliExpectation E p (T.indicator fun _ => 1) =
      finiteBernoulliProbability E p T := rfl
  have hTU : finiteBernoulliExpectation E p ((T ∩ U).indicator fun _ => 1) =
      finiteBernoulliProbability E p (T ∩ U) := rfl
  rw [hT', hTU] at h
  nlinarith [h]

/-- FKG for two decreasing events depending on finitely many coordinates. -/
theorem setBernoulli_real_fkg_of_decreasing_dependsOn (p : I) {E F : Finset ι}
    {A B : Set (Set ι)} (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real A * setBer((Set.univ : Set ι), p).real B ≤
      setBer((Set.univ : Set ι), p).real (A ∩ B) := by
  classical
  have hA' : DependsOn (E ∪ F) A := hA.mono Finset.subset_union_left
  have hB' : DependsOn (E ∪ F) B := hB.mono Finset.subset_union_right
  rw [hA'.setBernoulli_real_eq_finiteBernoulliProbability p,
    hB'.setBernoulli_real_eq_finiteBernoulliProbability p,
    (hA'.inter hB').setBernoulli_real_eq_finiteBernoulliProbability p]
  exact finiteBernoulliProbability_fkg_of_decreasing p.2.1 p.2.2
    hAdec.isDecreasingTrace_eventTrace hBdec.isDecreasingTrace_eventTrace

/-- Negative correlation of an increasing and a decreasing finitely supported event
(Grimmett p. 34: `E_p(XY) ≤ E_p(X)E_p(Y)` when `X` is increasing and `Y` decreasing). -/
theorem setBernoulli_real_le_mul_of_increasing_decreasing_dependsOn (p : I)
    {E F : Finset ι} {A B : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    setBer((Set.univ : Set ι), p).real (A ∩ B) ≤
      setBer((Set.univ : Set ι), p).real A * setBer((Set.univ : Set ι), p).real B := by
  classical
  have hA' : DependsOn (E ∪ F) A := hA.mono Finset.subset_union_left
  have hB' : DependsOn (E ∪ F) B := hB.mono Finset.subset_union_right
  rw [hA'.setBernoulli_real_eq_finiteBernoulliProbability p,
    hB'.setBernoulli_real_eq_finiteBernoulliProbability p,
    (hA'.inter hB').setBernoulli_real_eq_finiteBernoulliProbability p]
  exact finiteBernoulliProbability_le_mul_of_increasing_decreasing p.2.1 p.2.2
    hAinc.isIncreasingTrace_eventTrace hBdec.isDecreasingTrace_eventTrace

/-! ### The iterated inequality (2.7) -/

/-- A finite intersection of increasing events is increasing. -/
theorem isIncreasingEvent_biInter {κ : Type*} {J : Finset κ} {A : κ → Set (Set ι)}
    (hA : ∀ i ∈ J, IsIncreasingEvent (A i)) : IsIncreasingEvent (⋂ i ∈ J, A i) :=
  isIncreasingEvent_iInter fun i => isIncreasingEvent_iInter fun hi => hA i hi

/-- A finite intersection of events, each depending on finitely many coordinates, depends
on the union of the supports. -/
theorem dependsOn_biInter [DecidableEq ι] {κ : Type*} {J : Finset κ} {Ef : κ → Finset ι}
    {A : κ → Set (Set ι)} (hA : ∀ i ∈ J, DependsOn (Ef i) (A i)) :
    DependsOn (J.biUnion Ef) (⋂ i ∈ J, A i) := by
  intro ω η h
  simp only [Set.mem_iInter]
  refine forall₂_congr fun i hi => ?_
  exact hA i hi fun e he => h e (Finset.mem_biUnion.mpr ⟨i, hi, he⟩)

/-- **Iterated FKG inequality** (Grimmett (2.7)): finitely many increasing, finitely
supported events satisfy `∏ P(Aᵢ) ≤ P(⋂ Aᵢ)`. -/
theorem setBernoulli_prod_le_real_biInter_fkg {κ : Type*} (p : I) {J : Finset κ}
    {Ef : κ → Finset ι} {A : κ → Set (Set ι)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i)) (hA : ∀ i ∈ J, DependsOn (Ef i) (A i)) :
    ∏ i ∈ J, setBer((Set.univ : Set ι), p).real (A i) ≤
      setBer((Set.univ : Set ι), p).real (⋂ i ∈ J, A i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert a J ha ih =>
    have hstep := setBernoulli_real_fkg_of_dependsOn p (hAinc a (Finset.mem_insert_self a J))
      (isIncreasingEvent_biInter fun i hi => hAinc i (Finset.mem_insert_of_mem hi))
      (hA a (Finset.mem_insert_self a J))
      (dependsOn_biInter fun i hi => hA i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha]
    have hrest := ih (fun i hi => hAinc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hA i (Finset.mem_insert_of_mem hi))
    have hnonneg : 0 ≤ setBer((Set.univ : Set ι), p).real (A a) :=
      measureReal_nonneg
    calc setBer((Set.univ : Set ι), p).real (A a) *
          ∏ i ∈ J, setBer((Set.univ : Set ι), p).real (A i)
        ≤ setBer((Set.univ : Set ι), p).real (A a) *
          setBer((Set.univ : Set ι), p).real (⋂ i ∈ J, A i) :=
          mul_le_mul_of_nonneg_left hrest hnonneg
      _ ≤ setBer((Set.univ : Set ι), p).real (A a ∩ ⋂ i ∈ J, A i) := hstep
      _ = setBer((Set.univ : Set ι), p).real (⋂ i ∈ insert a J, A i) := by
          rw [Finset.set_biInter_insert]

/-! ### The observable form (Theorem 2.4(a), finite support) -/

/-- **FKG inequality for increasing finitely supported observables** (Grimmett Theorem
(2.4a) restricted to finite supports): `E_p(X) E_p(Y) ≤ E_p(XY)`. -/
theorem setBernoulli_integral_fkg_of_dependsOnFun (p : I) {E F : Finset ι}
    {X Y : Set ι → ℝ}
    (hXinc : IsIncreasingRandomVariable X) (hYinc : IsIncreasingRandomVariable Y)
    (hX : DependsOnFun E X) (hY : DependsOnFun F Y) :
    (∫ ω, X ω ∂ setBer((Set.univ : Set ι), p)) *
        (∫ ω, Y ω ∂ setBer((Set.univ : Set ι), p)) ≤
      ∫ ω, X ω * Y ω ∂ setBer((Set.univ : Set ι), p) := by
  classical
  have hX' : DependsOnFun (E ∪ F) X := hX.mono Finset.subset_union_left
  have hY' : DependsOnFun (E ∪ F) Y := hY.mono Finset.subset_union_right
  have hXY : DependsOnFun (E ∪ F) (fun ω => X ω * Y ω) := fun ω η h => by
    show X ω * Y ω = X η * Y η
    rw [hX' h, hY' h]
  rw [hX'.integral_setBernoulli p, hY'.integral_setBernoulli p,
    hXY.integral_setBernoulli p]
  exact finiteBernoulliExpectation_mul_fkg_of_monotone p.2.1 p.2.2
    (fun s t hst _ => hXinc (Finset.coe_subset.mpr hst))
    (fun s t hst _ => hYinc (Finset.coe_subset.mpr hst))

/-! ### Cubic lattice specializations -/

/-- **FKG inequality on the cubic lattice** for increasing finitely supported bond events
(Grimmett Theorem (2.4b), finite support). -/
theorem bernoulliBondMeasure_real_fkg_of_dependsOn {d : ℕ} (p : I)
    {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hBinc : IsIncreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_dependsOn p hAinc hBinc hA hB

/-- FKG on the cubic lattice for decreasing finitely supported bond events. -/
theorem bernoulliBondMeasure_real_fkg_of_decreasing_dependsOn {d : ℕ} (p : I)
    {E F : Finset (CubicEdge d)} {A B : Set (EdgeConfiguration d)}
    (hAdec : IsDecreasingEvent A) (hBdec : IsDecreasingEvent B)
    (hA : DependsOn E A) (hB : DependsOn F B) :
    (bernoulliBondMeasure d p).real A * (bernoulliBondMeasure d p).real B ≤
      (bernoulliBondMeasure d p).real (A ∩ B) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_real_fkg_of_decreasing_dependsOn p hAdec hBdec hA hB

/-- Iterated FKG (Grimmett (2.7)) on the cubic lattice. -/
theorem bernoulliBondMeasure_prod_le_real_biInter_fkg {d : ℕ} {κ : Type*} (p : I)
    {J : Finset κ} {Ef : κ → Finset (CubicEdge d)} {A : κ → Set (EdgeConfiguration d)}
    (hAinc : ∀ i ∈ J, IsIncreasingEvent (A i)) (hA : ∀ i ∈ J, DependsOn (Ef i) (A i)) :
    ∏ i ∈ J, (bernoulliBondMeasure d p).real (A i) ≤
      (bernoulliBondMeasure d p).real (⋂ i ∈ J, A i) := by
  simpa [bernoulliBondMeasure] using
    setBernoulli_prod_le_real_biInter_fkg p hAinc hA

end Percolation
