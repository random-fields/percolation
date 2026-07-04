import Percolation.Bernoulli.FiniteCube
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Russo's formula

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.4, pp. 41–46
(source id `grimmett-percolation-1999`).

This file develops pivotal coordinates and the derivative formulas of §2.4 on the finite
cube model of `Percolation.Bernoulli.FiniteCube`, then transfers them to the ambient product
measure `setBer((Set.univ : Set ι), p)`:

* `Percolation.IsPivotal`, `Percolation.pivotalEvent`, `Percolation.IsPivotalTrace`,
  `Percolation.pivotalTrace`, `Percolation.pivotalTraceCount` — Grimmett's pivotal edges and
  the pivotal count `N(A)` (p. 42), at the ambient and finite-trace levels;
* `Percolation.hasDerivAt_finiteBernoulliProbability_sum_pivotal` and
  `Percolation.hasDerivAt_finiteBernoulliProbability` — **Russo's formula** (Theorem 2.25,
  equations (2.26)/(2.27)): `d/dp P_p(A) = ∑_e P_p(e pivotal) = E_p(N(A))` for increasing
  finite traces;
* `Percolation.IsIncreasingEvent.hasDerivAt_setBernoulli_real` — the measure-level Russo
  formula for increasing events with finite support, with cubic-lattice wrapper
  `Percolation.IsIncreasingEvent.bernoulliBondMeasure_real_russo_hasDerivAt`;
* `Percolation.finiteBernoulliProbability_inter_pivotalTrace` and
  `Percolation.IsIncreasingEvent.setBernoulli_real_inter_pivotalEvent` — equation (2.29):
  `P_p(A ∩ {e pivotal}) = p · P_p(e pivotal)` for increasing events;
* `Percolation.finiteBernoulliProbability_le_ratio_pow_mul` and
  `Percolation.IsIncreasingEvent.setBernoulli_real_le_ratio_pow_mul` — inequality (2.31):
  `P_{p₂}(A) ≤ (p₂/p₁)^{|E|} P_{p₁}(A)` for `0 < p₁ ≤ p₂ ≤ 1`;
* `Percolation.traceDifference`, `Percolation.hasDerivAt_finiteBernoulliExpectation` —
  Theorem 2.32: `d/dp E_p(X) = ∑_e E_p(δ_e X)` for arbitrary observables (no monotonicity),
  with measure-level wrapper `Percolation.DependsOnFun.hasDerivAt_integral_setBernoulli`;
* `Percolation.traceSecondDifference`,
  `Percolation.hasDerivAt_sum_finiteBernoulliExpectation_traceDifference` and its
  diagonal-free variants — the second-derivative formula (2.33).
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped Finset unitInterval Classical

variable {ι : Type*}

/-! ### Pivotal coordinates -/

/-- The coordinate `e` is *pivotal* for the event `A` in the configuration `ω` when the state
of `e` decides membership: the configuration with `e` opened and the configuration with `e`
closed disagree about `A` (Grimmett p. 42). -/
def IsPivotal (A : Set (Set ι)) (e : ι) (ω : Set ι) : Prop :=
  ¬((insert e ω ∈ A) ↔ (ω \ {e} ∈ A))

/-- The event that `e` is pivotal for `A`. -/
def pivotalEvent (A : Set (Set ι)) (e : ι) : Set (Set ι) :=
  {ω | IsPivotal A e ω}

@[simp] theorem mem_pivotalEvent {A : Set (Set ι)} {e : ι} {ω : Set ι} :
    ω ∈ pivotalEvent A e ↔ IsPivotal A e ω :=
  Iff.rfl

/-- Finite-trace pivotality: the trace with `e` inserted and the trace with `e` erased
disagree about the trace event `T`. -/
def IsPivotalTrace (T : Set (Finset ι)) (e : ι) (s : Finset ι) : Prop :=
  ¬((insert e s ∈ T) ↔ (s.erase e ∈ T))

/-- The trace event that `e` is pivotal for `T`. -/
def pivotalTrace (T : Set (Finset ι)) (e : ι) : Set (Finset ι) :=
  {s | IsPivotalTrace T e s}

@[simp] theorem mem_pivotalTrace {T : Set (Finset ι)} {e : ι} {s : Finset ι} :
    s ∈ pivotalTrace T e ↔ IsPivotalTrace T e s :=
  Iff.rfl

/-- The number of coordinates of `E` pivotal for the trace event `T` in the trace `s` — this
is Grimmett's pivotal count `N(A)` (p. 43) restricted to the finite support `E`, as a real
observable on the finite cube. -/
noncomputable def pivotalTraceCount (E : Finset ι) (T : Set (Finset ι)) (s : Finset ι) : ℝ :=
  ((E.filter fun e => IsPivotalTrace T e s).card : ℝ)

/-- Grimmett's finite difference operator `δ_e X (ω) = X(ω ∪ {e}) - X(ω \ {e})` (p. 45), on
finite traces. -/
noncomputable def traceDifference (e : ι) (X : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  X (insert e s) - X (s.erase e)

/-- Iterated finite difference `δ_e δ_f X` (Grimmett p. 46). -/
noncomputable def traceSecondDifference (e f : ι) (X : Finset ι → ℝ) : Finset ι → ℝ :=
  traceDifference e (traceDifference f X)

/-! ### Insensitivity to the pivotal coordinate -/

/-- Pivotality of `e` does not depend on the state of `e` itself: opening `e` first changes
nothing. -/
theorem isPivotal_insert (A : Set (Set ι)) (e : ι) (ω : Set ι) :
    IsPivotal A e (insert e ω) ↔ IsPivotal A e ω := by
  unfold IsPivotal
  rw [Set.insert_idem, Set.insert_diff_of_mem _ (Set.mem_singleton e)]

/-- Pivotality of `e` does not depend on the state of `e` itself: closing `e` first changes
nothing. -/
theorem isPivotal_diff_singleton (A : Set (Set ι)) (e : ι) (ω : Set ι) :
    IsPivotal A e (ω \ {e}) ↔ IsPivotal A e ω := by
  unfold IsPivotal
  rw [Set.insert_diff_singleton, sdiff_idem]

/-- Auxiliary `Finset` identity: reinserting an erased element yields the plain insertion. -/
theorem insert_erase_self (e : ι) (s : Finset ι) : insert e (s.erase e) = insert e s := by
  by_cases h : e ∈ s
  · rw [Finset.insert_erase h, Finset.insert_eq_of_mem h]
  · rw [Finset.erase_eq_of_notMem h]

/-- Trace pivotality of `e` does not depend on the state of `e` itself: inserting `e` first
changes nothing. -/
theorem isPivotalTrace_insert (T : Set (Finset ι)) (e : ι) (s : Finset ι) :
    IsPivotalTrace T e (insert e s) ↔ IsPivotalTrace T e s := by
  unfold IsPivotalTrace
  rw [Finset.insert_idem, Finset.erase_insert_eq_erase]

/-- Trace pivotality of `e` does not depend on the state of `e` itself: erasing `e` first
changes nothing. -/
theorem isPivotalTrace_erase (T : Set (Finset ι)) (e : ι) (s : Finset ι) :
    IsPivotalTrace T e (s.erase e) ↔ IsPivotalTrace T e s := by
  unfold IsPivotalTrace
  rw [insert_erase_self, Finset.erase_idem]

/-! ### Pivotality for increasing events -/

/-- For an increasing event, `e` is pivotal exactly when opening `e` realizes the event while
closing `e` prevents it (Grimmett p. 42). -/
theorem IsIncreasingEvent.isPivotal_iff {A : Set (Set ι)} (hA : IsIncreasingEvent A)
    (e : ι) (ω : Set ι) :
    IsPivotal A e ω ↔ insert e ω ∈ A ∧ ω \ {e} ∉ A := by
  have hmono : ω \ {e} ∈ A → insert e ω ∈ A := fun h =>
    hA (Set.diff_subset.trans (Set.subset_insert e ω)) h
  unfold IsPivotal
  constructor
  · intro h
    by_cases h1 : insert e ω ∈ A
    · exact ⟨h1, fun h2 => h (iff_of_true h1 h2)⟩
    · exact absurd (iff_of_false h1 fun h2 => h1 (hmono h2)) h
  · rintro ⟨h1, h2⟩ hiff
    exact h2 (hiff.mp h1)

/-- For an increasing trace event, `e` is pivotal exactly when inserting `e` realizes the
event while erasing `e` prevents it. -/
theorem IsIncreasingTrace.isPivotalTrace_iff {T : Set (Finset ι)} (hT : IsIncreasingTrace T)
    (e : ι) (s : Finset ι) :
    IsPivotalTrace T e s ↔ insert e s ∈ T ∧ s.erase e ∉ T := by
  have hmono : s.erase e ∈ T → insert e s ∈ T := fun h =>
    hT ((Finset.erase_subset e s).trans (Finset.subset_insert e s)) h
  unfold IsPivotalTrace
  constructor
  · intro h
    by_cases h1 : insert e s ∈ T
    · exact ⟨h1, fun h2 => h (iff_of_true h1 h2)⟩
    · exact absurd (iff_of_false h1 fun h2 => h1 (hmono h2)) h
  · rintro ⟨h1, h2⟩ hiff
    exact h2 (hiff.mp h1)

/-! ### Support of the pivotal event -/

/-- If `A` depends on the coordinates in `E`, so does each pivotal event. -/
theorem DependsOn.pivotalEvent {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A)
    (e : ι) : DependsOn E (Percolation.pivotalEvent A e) := by
  intro ω η h
  have hopen : insert e ω ∈ A ↔ insert e η ∈ A := by
    refine hA fun f hf => ?_
    rcases eq_or_ne f e with rfl | hfe
    · simp
    · simp only [Set.mem_insert_iff, hfe, false_or]
      exact h f hf
  have hclosed : ω \ {e} ∈ A ↔ η \ {e} ∈ A := by
    refine hA fun f hf => ?_
    rcases eq_or_ne f e with rfl | hfe
    · simp
    · simp only [Set.mem_diff, Set.mem_singleton_iff, hfe, not_false_iff, and_true]
      exact h f hf
  exact not_congr (iff_congr hopen hclosed)

/-- No coordinate outside the support of an event is ever pivotal for it. -/
theorem pivotalEvent_eq_empty_of_notMem {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) {e : ι} (he : e ∉ E) : pivotalEvent A e = ∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false, iff_false, mem_pivotalEvent]
  intro hpiv
  refine hpiv (hA fun f hf => ?_)
  have hfe : f ≠ e := fun h => he (h ▸ hf)
  simp [Set.mem_insert_iff, Set.mem_diff, hfe]

/-- Traces of pivotal events are pivotal traces: the finite-trace pivotal event of the trace
of `A` is the trace of the pivotal event of `A`. -/
theorem eventTrace_pivotalEvent (A : Set (Set ι)) (e : ι) :
    eventTrace (pivotalEvent A e) = pivotalTrace (eventTrace A) e := by
  ext s
  simp only [mem_eventTrace, mem_pivotalTrace, mem_pivotalEvent, IsPivotal, IsPivotalTrace,
    Finset.coe_insert, Finset.coe_erase]

/-! ### The one-coordinate insert splitting of the finite model -/

/-- Adjoining a closed coordinate multiplies the weight by `1 - p`. -/
theorem finiteBernoulliWeight_insert_of_notMem {E : Finset ι} {a : ι} (ha : a ∉ E)
    {s : Finset ι} (hs : s ⊆ E) (p : ℝ) :
    finiteBernoulliWeight (insert a E) p s = (1 - p) * finiteBernoulliWeight E p s := by
  rw [finiteBernoulliWeight, finiteBernoulliWeight, Finset.card_insert_of_notMem ha,
    Nat.sub_add_comm (Finset.card_le_card hs), pow_succ]
  ring

/-- Adjoining an open coordinate multiplies the weight by `p`. -/
theorem finiteBernoulliWeight_insert_insert {E : Finset ι} {a : ι} (ha : a ∉ E)
    {s : Finset ι} (has : a ∉ s) (p : ℝ) :
    finiteBernoulliWeight (insert a E) p (insert a s) = p * finiteBernoulliWeight E p s := by
  rw [finiteBernoulliWeight, finiteBernoulliWeight, Finset.card_insert_of_notMem ha,
    Finset.card_insert_of_notMem has, Nat.add_sub_add_right, pow_succ]
  ring

/-- **Insert splitting for expectations**: conditioning on the state of a fresh coordinate
`a` splits the finite expectation into the open and closed sections. -/
theorem finiteBernoulliExpectation_insert {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ)
    (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p X =
      p * finiteBernoulliExpectation E p (fun s => X (insert a s)) +
        (1 - p) * finiteBernoulliExpectation E p X := by
  have hdisj : Disjoint E.powerset (E.powerset.image (insert a)) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    rcases Finset.mem_image.mp hti with ⟨s, _, rfl⟩
    exact ha (Finset.mem_powerset.mp ht (Finset.mem_insert_self a s))
  have hinj : ∀ s ∈ E.powerset, ∀ t ∈ E.powerset, insert a s = insert a t → s = t := by
    intro s hs t ht hst
    have has : a ∉ s := fun h => ha (Finset.mem_powerset.mp hs h)
    have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
    rw [← Finset.erase_insert has, ← Finset.erase_insert hat, hst]
  rw [finiteBernoulliExpectation, Finset.powerset_insert, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  have h1 : ∀ s ∈ E.powerset,
      finiteBernoulliWeight (insert a E) p s * X s =
        (1 - p) * (finiteBernoulliWeight E p s * X s) := by
    intro s hs
    rw [finiteBernoulliWeight_insert_of_notMem ha (Finset.mem_powerset.mp hs)]
    ring
  have h2 : ∀ s ∈ E.powerset,
      finiteBernoulliWeight (insert a E) p (insert a s) * X (insert a s) =
        p * (finiteBernoulliWeight E p s * X (insert a s)) := by
    intro s hs
    rw [finiteBernoulliWeight_insert_insert ha fun h => ha (Finset.mem_powerset.mp hs h)]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
    finiteBernoulliExpectation, finiteBernoulliExpectation]
  ring

/-- Finite expectations are additive under pointwise subtraction. -/
theorem finiteBernoulliExpectation_sub (E : Finset ι) (p : ℝ) (X Y : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s => X s - Y s) =
      finiteBernoulliExpectation E p X - finiteBernoulliExpectation E p Y := by
  rw [finiteBernoulliExpectation, finiteBernoulliExpectation, finiteBernoulliExpectation,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => mul_sub _ _ _

/-- Trace events agreeing on the powerset of the support have the same probability. -/
theorem finiteBernoulliProbability_congr {E : Finset ι} (p : ℝ) {T U : Set (Finset ι)}
    (h : ∀ s ∈ E.powerset, (s ∈ T ↔ s ∈ U)) :
    finiteBernoulliProbability E p T = finiteBernoulliProbability E p U :=
  finiteBernoulliExpectation_congr fun s hs => by
    by_cases hsT : s ∈ T
    · rw [Set.indicator_of_mem hsT, Set.indicator_of_mem ((h s hs).mp hsT)]
    · rw [Set.indicator_of_notMem hsT,
        Set.indicator_of_notMem fun hsU => hsT ((h s hs).mpr hsU)]

/-- **Insert splitting for probabilities**: conditioning on the state of a fresh coordinate
`a` splits the finite probability into the open section `{s | insert a s ∈ T}` and the
closed section, which reads as `T` itself on the powerset of `E`. -/
theorem finiteBernoulliProbability_insert {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliProbability (insert a E) p T =
      p * finiteBernoulliProbability E p {s : Finset ι | insert a s ∈ T} +
        (1 - p) * finiteBernoulliProbability E p T := by
  have h1 : finiteBernoulliExpectation E p
      (fun s => T.indicator (fun _ => (1 : ℝ)) (insert a s)) =
        finiteBernoulliExpectation E p
          ({s : Finset ι | insert a s ∈ T}.indicator fun _ => (1 : ℝ)) :=
    finiteBernoulliExpectation_congr fun s _ => by
      by_cases h : insert a s ∈ T <;> simp [h]
  rw [finiteBernoulliProbability, finiteBernoulliExpectation_insert ha, h1]
  rfl

/-- A trace event insensitive to the coordinate `a` has the same probability on the enlarged
support `insert a E`. -/
theorem finiteBernoulliProbability_insert_of_insert_iff {E : Finset ι} {a : ι} (ha : a ∉ E)
    (p : ℝ) {U : Set (Finset ι)} (hU : ∀ s : Finset ι, insert a s ∈ U ↔ s ∈ U) :
    finiteBernoulliProbability (insert a E) p U = finiteBernoulliProbability E p U := by
  have hset : {s : Finset ι | insert a s ∈ U} = U := Set.ext fun s => hU s
  rw [finiteBernoulliProbability_insert ha, hset]
  ring

/-- Intersecting an `a`-insensitive trace event with the event that `a` is open multiplies
the probability by `p` — the independence computation behind Grimmett's (2.29). -/
theorem finiteBernoulliProbability_insert_open_inter {E : Finset ι} {a : ι} (ha : a ∉ E)
    (p : ℝ) {U : Set (Finset ι)} (hU : ∀ s : Finset ι, insert a s ∈ U ↔ s ∈ U) :
    finiteBernoulliProbability (insert a E) p ({s : Finset ι | a ∈ s} ∩ U) =
      p * finiteBernoulliProbability E p U := by
  rw [finiteBernoulliProbability_insert ha]
  have h1 : {s : Finset ι | insert a s ∈ ({s : Finset ι | a ∈ s} ∩ U)} = U := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_insert_self, true_and]
    exact hU s
  have h2 : finiteBernoulliProbability E p ({s : Finset ι | a ∈ s} ∩ U) =
      finiteBernoulliProbability E p (∅ : Set (Finset ι)) :=
    finiteBernoulliProbability_congr p fun s hs =>
      iff_of_false (fun hmem => ha (Finset.mem_powerset.mp hs hmem.1)) (Set.notMem_empty s)
  rw [h1, h2, finiteBernoulliProbability_empty, mul_zero, add_zero]

/-! ### Theorem 2.32: the derivative of finite expectations -/

/-- The expected fresh-coordinate difference is the difference of the section expectations. -/
theorem finiteBernoulliExpectation_traceDifference_notMem {E : Finset ι} {a : ι}
    (ha : a ∉ E) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p (traceDifference a X) =
      finiteBernoulliExpectation E p (fun s => X (insert a s)) -
        finiteBernoulliExpectation E p X := by
  rw [finiteBernoulliExpectation_insert ha]
  have h1 : finiteBernoulliExpectation E p (fun s => traceDifference a X (insert a s)) =
      finiteBernoulliExpectation E p (traceDifference a X) :=
    finiteBernoulliExpectation_congr fun s _ => by
      rw [traceDifference, traceDifference, Finset.insert_idem, Finset.erase_insert_eq_erase]
  have h2 : finiteBernoulliExpectation E p (traceDifference a X) =
      finiteBernoulliExpectation E p (fun s => X (insert a s) - X s) :=
    finiteBernoulliExpectation_congr fun s hs => by
      rw [traceDifference, Finset.erase_eq_of_notMem
        fun h => ha (Finset.mem_powerset.mp hs h)]
  rw [h1, h2, finiteBernoulliExpectation_sub]
  ring

/-- The difference operator in an old coordinate commutes with sectioning a fresh one. -/
theorem traceDifference_insert_of_ne {a e : ι} (hae : a ≠ e) (X : Finset ι → ℝ)
    (s : Finset ι) :
    traceDifference e X (insert a s) = traceDifference e (fun u => X (insert a u)) s := by
  rw [traceDifference, traceDifference, Finset.insert_comm e a,
    Finset.erase_insert_of_ne hae]

/-- Insert splitting for the expected difference in an old coordinate. -/
theorem finiteBernoulliExpectation_traceDifference_insert {E : Finset ι} {a e : ι}
    (ha : a ∉ E) (hae : a ≠ e) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p (traceDifference e X) =
      p * finiteBernoulliExpectation E p (traceDifference e (fun s => X (insert a s))) +
        (1 - p) * finiteBernoulliExpectation E p (traceDifference e X) := by
  have h : finiteBernoulliExpectation E p (fun s => traceDifference e X (insert a s)) =
      finiteBernoulliExpectation E p (traceDifference e (fun s => X (insert a s))) :=
    finiteBernoulliExpectation_congr fun s _ => traceDifference_insert_of_ne hae X s
  rw [finiteBernoulliExpectation_insert ha, h]

/-- **Theorem 2.32 (finite form).** The expectation of an arbitrary finite-cube observable is
differentiable in the density, with derivative the sum of the expected finite differences:
`d/dp E_p(X) = ∑_{e ∈ E} E_p(δ_e X)`. No monotonicity is assumed. -/
theorem hasDerivAt_finiteBernoulliExpectation {E : Finset ι} (X : Finset ι → ℝ) (p : ℝ) :
    HasDerivAt (fun x : ℝ => finiteBernoulliExpectation E x X)
      (∑ e ∈ E, finiteBernoulliExpectation E p (traceDifference e X)) p := by
  induction E using Finset.induction generalizing X with
  | empty =>
      have h : (fun x : ℝ => finiteBernoulliExpectation (∅ : Finset ι) x X) =
          fun _ => X ∅ := by
        funext x
        simp [finiteBernoulliExpectation, finiteBernoulliWeight]
      rw [Finset.sum_empty, h]
      exact hasDerivAt_const p (X ∅)
  | insert a E ha ih =>
      have hsplit : (fun x : ℝ => finiteBernoulliExpectation (insert a E) x X) =
          fun x : ℝ => x * finiteBernoulliExpectation E x (fun s => X (insert a s)) +
            (1 - x) * finiteBernoulliExpectation E x X := by
        funext x
        exact finiteBernoulliExpectation_insert ha x X
      rw [hsplit]
      have hderiv := ((hasDerivAt_id p).mul (ih (fun s => X (insert a s)))).add
        (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).mul (ih X))
      refine hderiv.congr_deriv ?_
      rw [Finset.sum_insert ha, finiteBernoulliExpectation_traceDifference_notMem ha p X,
        Finset.sum_congr rfl fun e he => finiteBernoulliExpectation_traceDifference_insert
          ha (fun h => ha (h ▸ he)) p X,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [Pi.sub_apply, id_eq]
      ring

/-! ### Theorem 2.25: Russo's formula on the finite cube -/

/-- For an increasing trace event, the finite difference of the indicator is exactly the
indicator of the pivotal trace: `δ_e 1_T = 1_{e pivotal for T}`. -/
theorem IsIncreasingTrace.traceDifference_indicator {T : Set (Finset ι)}
    (hT : IsIncreasingTrace T) (e : ι) (s : Finset ι) :
    traceDifference e (T.indicator fun _ => (1 : ℝ)) s =
      (pivotalTrace T e).indicator (fun _ => (1 : ℝ)) s := by
  have hmono : s.erase e ∈ T → insert e s ∈ T := fun h =>
    hT ((Finset.erase_subset e s).trans (Finset.subset_insert e s)) h
  by_cases h1 : insert e s ∈ T <;> by_cases h2 : s.erase e ∈ T
  · have hnp : s ∉ pivotalTrace T e := fun hp => hp (iff_of_true h1 h2)
    rw [traceDifference, Set.indicator_of_mem h1, Set.indicator_of_mem h2,
      Set.indicator_of_notMem hnp, sub_self]
  · have hp : s ∈ pivotalTrace T e := fun hiff => h2 (hiff.mp h1)
    rw [traceDifference, Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
      Set.indicator_of_mem hp, sub_zero]
  · exact absurd (hmono h2) h1
  · have hnp : s ∉ pivotalTrace T e := fun hp => hp (iff_of_false h1 h2)
    rw [traceDifference, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
      Set.indicator_of_notMem hnp, sub_self]

/-- **Russo's formula, finite form (Theorem 2.25, equation (2.27)).** For an increasing
trace event, `d/dp P_p(T) = ∑_{e ∈ E} P_p(e pivotal for T)`. -/
theorem hasDerivAt_finiteBernoulliProbability_sum_pivotal {E : Finset ι}
    {T : Set (Finset ι)} (hT : IsIncreasingTrace T) (p : ℝ) :
    HasDerivAt (fun x : ℝ => finiteBernoulliProbability E x T)
      (∑ e ∈ E, finiteBernoulliProbability E p (pivotalTrace T e)) p := by
  have h := hasDerivAt_finiteBernoulliExpectation (E := E) (T.indicator fun _ => (1 : ℝ)) p
  have hderiv : ∑ e ∈ E, finiteBernoulliExpectation E p
      (traceDifference e (T.indicator fun _ => (1 : ℝ))) =
        ∑ e ∈ E, finiteBernoulliProbability E p (pivotalTrace T e) :=
    Finset.sum_congr rfl fun e _ =>
      finiteBernoulliExpectation_congr fun s _ => hT.traceDifference_indicator e s
  rw [hderiv] at h
  exact h

/-- The pivotal count decomposes as a sum of pivotal-trace indicators. -/
theorem pivotalTraceCount_eq_sum_indicator (E : Finset ι) (T : Set (Finset ι))
    (s : Finset ι) :
    pivotalTraceCount E T s =
      ∑ e ∈ E, (pivotalTrace T e).indicator (fun _ => (1 : ℝ)) s := by
  rw [pivotalTraceCount, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : IsPivotalTrace T e s
  · rw [if_pos h, Set.indicator_of_mem (mem_pivotalTrace.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem fun hs => h (mem_pivotalTrace.mp hs)]

/-- Equation (2.26) = equation (2.27): the sum of the pivotal probabilities is the expected
pivotal count `E_p(N)`. -/
theorem sum_finiteBernoulliProbability_pivotalTrace (E : Finset ι) (p : ℝ)
    (T : Set (Finset ι)) :
    ∑ e ∈ E, finiteBernoulliProbability E p (pivotalTrace T e) =
      finiteBernoulliExpectation E p (pivotalTraceCount E T) := by
  have h : ∀ s ∈ E.powerset,
      finiteBernoulliWeight E p s * pivotalTraceCount E T s =
        ∑ e ∈ E, finiteBernoulliWeight E p s *
          (pivotalTrace T e).indicator (fun _ => (1 : ℝ)) s := by
    intro s _
    rw [pivotalTraceCount_eq_sum_indicator, Finset.mul_sum]
  rw [finiteBernoulliExpectation, Finset.sum_congr rfl h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => rfl

/-- **Russo's formula, finite form (Theorem 2.25, equation (2.26)).** For an increasing
trace event, `d/dp P_p(T) = E_p(N(T))`, the expected number of pivotal coordinates. -/
theorem hasDerivAt_finiteBernoulliProbability {E : Finset ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace T) (p : ℝ) :
    HasDerivAt (fun x : ℝ => finiteBernoulliProbability E x T)
      (finiteBernoulliExpectation E p (pivotalTraceCount E T)) p := by
  have h := hasDerivAt_finiteBernoulliProbability_sum_pivotal (E := E) hT p
  rwa [sum_finiteBernoulliProbability_pivotalTrace] at h

/-! ### Equation (2.29): pivotality is independent of the pivotal coordinate -/

/-- **Equation (2.29), finite form.** For an increasing trace event and `e ∈ E`,
`P_p(T ∩ {e pivotal}) = p · P_p(e pivotal)`: on the pivotal event, `T` occurs exactly when
`e` is open, and pivotality is independent of the state of `e`. Valid for every real `p`. -/
theorem finiteBernoulliProbability_inter_pivotalTrace {E : Finset ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace T) {e : ι} (he : e ∈ E) (p : ℝ) :
    finiteBernoulliProbability E p (T ∩ pivotalTrace T e) =
      p * finiteBernoulliProbability E p (pivotalTrace T e) := by
  have hU : ∀ s : Finset ι, insert e s ∈ pivotalTrace T e ↔ s ∈ pivotalTrace T e :=
    fun s => isPivotalTrace_insert T e s
  have hset : T ∩ pivotalTrace T e = {s : Finset ι | e ∈ s} ∩ pivotalTrace T e := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_pivotalTrace]
    constructor
    · rintro ⟨hsT, hpiv⟩
      refine ⟨?_, hpiv⟩
      by_contra hes
      exact ((hT.isPivotalTrace_iff e s).mp hpiv).2
        (by rwa [Finset.erase_eq_of_notMem hes])
    · rintro ⟨hes, hpiv⟩
      refine ⟨?_, hpiv⟩
      have h1 := ((hT.isPivotalTrace_iff e s).mp hpiv).1
      rwa [Finset.insert_eq_of_mem hes] at h1
  rw [hset, ← Finset.insert_erase he,
    finiteBernoulliProbability_insert_open_inter (Finset.notMem_erase e E) p hU,
    finiteBernoulliProbability_insert_of_insert_iff (Finset.notMem_erase e E) p hU]

/-! ### Transfer to the ambient product measure -/

/-- Traces commute with intersections. -/
theorem eventTrace_inter (A B : Set (Set ι)) :
    eventTrace (A ∩ B) = eventTrace A ∩ eventTrace B :=
  rfl

/-- Transfer of pivotal probabilities: the ambient probability that `e` is pivotal for a
finitely supported event is the finite-cube probability of the pivotal trace. -/
theorem DependsOn.setBernoulli_real_pivotalEvent {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (e : ι) (p : I) :
    setBer((Set.univ : Set ι), p).real (Percolation.pivotalEvent A e) =
      finiteBernoulliProbability E (p : ℝ) (pivotalTrace (eventTrace A) e) := by
  rw [(hA.pivotalEvent e).setBernoulli_real_eq_finiteBernoulliProbability p,
    eventTrace_pivotalEvent]

/-- **Equation (2.29).** For an increasing event depending on `E` and `e ∈ E`,
`P_p(A ∩ {e pivotal}) = p · P_p(e pivotal)`. -/
theorem IsIncreasingEvent.setBernoulli_real_inter_pivotalEvent {E : Finset ι}
    {A : Set (Set ι)} (hAinc : IsIncreasingEvent A) (hA : DependsOn E A) {e : ι}
    (he : e ∈ E) (p : I) :
    setBer((Set.univ : Set ι), p).real (A ∩ pivotalEvent A e) =
      (p : ℝ) * setBer((Set.univ : Set ι), p).real (pivotalEvent A e) := by
  rw [(hA.inter (hA.pivotalEvent e)).setBernoulli_real_eq_finiteBernoulliProbability p,
    hA.setBernoulli_real_pivotalEvent e p, eventTrace_inter, eventTrace_pivotalEvent]
  exact finiteBernoulliProbability_inter_pivotalTrace
    hAinc.isIncreasingTrace_eventTrace he (p : ℝ)

/-- Equation (2.29) for the cubic-lattice Bernoulli bond measure. -/
theorem IsIncreasingEvent.bernoulliBondMeasure_real_inter_pivotalEvent {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hA : DependsOn E A) {e : CubicEdge d} (he : e ∈ E)
    (p : I) :
    (bernoulliBondMeasure d p).real (A ∩ pivotalEvent A e) =
      (p : ℝ) * (bernoulliBondMeasure d p).real (pivotalEvent A e) := by
  simpa [bernoulliBondMeasure] using
    hAinc.setBernoulli_real_inter_pivotalEvent hA he p

/-- **Russo's formula (Theorem 2.25).** For an increasing event depending on the finite
coordinate set `E`, the map `p ↦ P_p(A)` is differentiable on `(0, 1)` with derivative the
sum of the pivotal probabilities: `d/dp P_p(A) = ∑_{e ∈ E} P_p(e pivotal for A)`. The
density is clamped to `[0,1]` by `Set.projIcc` so that the function is defined on all
of `ℝ`. -/
theorem IsIncreasingEvent.hasDerivAt_setBernoulli_real {E : Finset ι} {A : Set (Set ι)}
    (hAinc : IsIncreasingEvent A) (hA : DependsOn E A) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasDerivAt
      (fun x : ℝ => setBer((Set.univ : Set ι), Set.projIcc 0 1 zero_le_one x).real A)
      (∑ e ∈ E, setBer((Set.univ : Set ι), p).real (pivotalEvent A e)) (p : ℝ) := by
  have hfin := hasDerivAt_finiteBernoulliProbability_sum_pivotal (E := E)
    hAinc.isIncreasingTrace_eventTrace (p : ℝ)
  have hderiv : ∑ e ∈ E, setBer((Set.univ : Set ι), p).real (pivotalEvent A e) =
      ∑ e ∈ E, finiteBernoulliProbability E (p : ℝ) (pivotalTrace (eventTrace A) e) :=
    Finset.sum_congr rfl fun e _ => hA.setBernoulli_real_pivotalEvent e p
  rw [hderiv]
  refine hfin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hp0 hp1] with x hx
  have hcoe : ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ) = x := by
    rw [Set.coe_projIcc, min_eq_right hx.2.le, max_eq_right hx.1.le]
  rw [hA.setBernoulli_real_eq_finiteBernoulliProbability (Set.projIcc 0 1 zero_le_one x),
    hcoe]

/-- Russo's formula (Theorem 2.25) for the cubic-lattice Bernoulli bond measure. -/
theorem IsIncreasingEvent.bernoulliBondMeasure_real_russo_hasDerivAt {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hAinc : IsIncreasingEvent A) (hA : DependsOn E A) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasDerivAt
      (fun x : ℝ => (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one x)).real A)
      (∑ e ∈ E, (bernoulliBondMeasure d p).real (pivotalEvent A e)) (p : ℝ) := by
  simpa [bernoulliBondMeasure] using hAinc.hasDerivAt_setBernoulli_real hA hp0 hp1

/-! ### Inequality (2.31) -/

/-- **Inequality (2.31), finite form.** For an increasing trace event and
`0 < p₁ ≤ p₂ ≤ 1`, `P_{p₂}(T) ≤ (p₂/p₁)^{|E|} · P_{p₁}(T)`: the map
`p ↦ p^{-|E|} P_p(T)` is antitone, by Russo's formula and equation (2.29). -/
theorem finiteBernoulliProbability_le_ratio_pow_mul {E : Finset ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace T) {p₁ p₂ : ℝ}
    (h0 : 0 < p₁) (h12 : p₁ ≤ p₂) (h21 : p₂ ≤ 1) :
    finiteBernoulliProbability E p₂ T ≤
      (p₂ / p₁) ^ E.card * finiteBernoulliProbability E p₁ T := by
  rcases Finset.eq_empty_or_nonempty E with rfl | hE
  · have h : ∀ x : ℝ, finiteBernoulliProbability (∅ : Finset ι) x T =
        T.indicator (fun _ => (1 : ℝ)) ∅ := fun x => by
      simp [finiteBernoulliProbability, finiteBernoulliExpectation, finiteBernoulliWeight]
    rw [h p₁, h p₂, Finset.card_empty, pow_zero, one_mul]
  · have hm0 : 0 < E.card := Finset.card_pos.mpr hE
    have h02 : 0 < p₂ := h0.trans_le h12
    have hfd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => finiteBernoulliProbability E y T)
        (∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e)) x := fun x =>
      hasDerivAt_finiteBernoulliProbability_sum_pivotal hT x
    have hfdiff : Differentiable ℝ fun y : ℝ => finiteBernoulliProbability E y T :=
      fun x => (hfd x).differentiableAt
    have hfc : Continuous fun y : ℝ => finiteBernoulliProbability E y T :=
      hfdiff.continuous
    have hkey : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        x * ∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e) ≤
          (E.card : ℝ) * finiteBernoulliProbability E x T := by
      intro x hx0 hx1
      have h1 : x * ∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e) =
          ∑ e ∈ E, finiteBernoulliProbability E x (T ∩ pivotalTrace T e) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e he =>
          (finiteBernoulliProbability_inter_pivotalTrace hT he x).symm
      rw [h1]
      calc ∑ e ∈ E, finiteBernoulliProbability E x (T ∩ pivotalTrace T e)
          ≤ ∑ e ∈ E, finiteBernoulliProbability E x T :=
            Finset.sum_le_sum fun e _ =>
              finiteBernoulliProbability_mono hx0 hx1 Set.inter_subset_left
        _ = (E.card : ℝ) * finiteBernoulliProbability E x T := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hanti : AntitoneOn
        (fun y : ℝ => finiteBernoulliProbability E y T / y ^ E.card)
        (Set.Icc p₁ p₂) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc p₁ p₂)
        (hfc.continuousOn.div (continuous_pow E.card).continuousOn fun x hx =>
          pow_ne_zero E.card (h0.trans_le hx.1).ne')
        (f' := fun x =>
          ((∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e)) * x ^ E.card -
            finiteBernoulliProbability E x T * ((E.card : ℝ) * x ^ (E.card - 1))) /
              (x ^ E.card) ^ 2)
        ?_ ?_
      · intro x hx
        rw [interior_Icc] at hx
        exact ((hfd x).div (hasDerivAt_pow E.card x)
          (pow_ne_zero E.card (h0.trans hx.1).ne')).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := h0.trans hx.1
        have hx1 : x ≤ 1 := hx.2.le.trans h21
        refine div_nonpos_iff.mpr (Or.inr ⟨?_, sq_nonneg _⟩)
        have hxm : x ^ E.card = x ^ (E.card - 1) * x := by
          rw [← pow_succ, Nat.sub_add_cancel hm0]
        have hb := hkey x hx0.le hx1
        calc (∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e)) * x ^ E.card -
              finiteBernoulliProbability E x T * ((E.card : ℝ) * x ^ (E.card - 1))
            = x ^ (E.card - 1) *
                (x * ∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e) -
                  (E.card : ℝ) * finiteBernoulliProbability E x T) := by
              rw [hxm]; ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0.le _) (by linarith)
    have hgle := hanti (Set.left_mem_Icc.mpr h12) (Set.right_mem_Icc.mpr h12) h12
    have hp1m : (0 : ℝ) < p₁ ^ E.card := pow_pos h0 _
    have hp2m : (0 : ℝ) < p₂ ^ E.card := pow_pos h02 _
    rw [div_le_div_iff₀ hp2m hp1m] at hgle
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hp1m]
    exact hgle.trans_eq (mul_comm _ _)

/-- **Inequality (2.31).** For an increasing event depending on `E` and densities
`0 < p₁ ≤ p₂` in the unit interval, `P_{p₂}(A) ≤ (p₂/p₁)^{|E|} · P_{p₁}(A)`. -/
theorem IsIncreasingEvent.setBernoulli_real_le_ratio_pow_mul {E : Finset ι}
    {A : Set (Set ι)} (hAinc : IsIncreasingEvent A) (hA : DependsOn E A) {p₁ p₂ : I}
    (h0 : 0 < (p₁ : ℝ)) (h12 : (p₁ : ℝ) ≤ (p₂ : ℝ)) :
    setBer((Set.univ : Set ι), p₂).real A ≤
      ((p₂ : ℝ) / (p₁ : ℝ)) ^ E.card * setBer((Set.univ : Set ι), p₁).real A := by
  rw [hA.setBernoulli_real_eq_finiteBernoulliProbability p₂,
    hA.setBernoulli_real_eq_finiteBernoulliProbability p₁]
  exact finiteBernoulliProbability_le_ratio_pow_mul
    hAinc.isIncreasingTrace_eventTrace h0 h12 p₂.2.2

/-! ### Theorem 2.32, measure level -/

/-- **Theorem 2.32, measure level.** The integral of a finitely supported observable is
differentiable in the density, with derivative the sum of the expected finite differences of
its trace. -/
theorem DependsOnFun.hasDerivAt_integral_setBernoulli {E : Finset ι} {X : Set ι → ℝ}
    (hX : DependsOnFun E X) {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    HasDerivAt
      (fun x : ℝ => ∫ ω, X ω ∂ setBer((Set.univ : Set ι), Set.projIcc 0 1 zero_le_one x))
      (∑ e ∈ E, finiteBernoulliExpectation E (p : ℝ)
        (traceDifference e fun s => X (↑s : Set ι))) (p : ℝ) := by
  have hfin := hasDerivAt_finiteBernoulliExpectation (E := E)
    (fun s => X (↑s : Set ι)) (p : ℝ)
  refine hfin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hp0 hp1] with x hx
  have hcoe : ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ) = x := by
    rw [Set.coe_projIcc, min_eq_right hx.2.le, max_eq_right hx.1.le]
  rw [hX.integral_setBernoulli (Set.projIcc 0 1 zero_le_one x), hcoe]

/-! ### The second-derivative formula (2.33) -/

/-- The diagonal second difference vanishes: `δ_e δ_e X = 0`. -/
theorem traceSecondDifference_self (e : ι) (X : Finset ι → ℝ) (s : Finset ι) :
    traceSecondDifference e e X s = 0 := by
  rw [traceSecondDifference, traceDifference, traceDifference, traceDifference,
    Finset.insert_idem, Finset.erase_insert_eq_erase, insert_erase_self, Finset.erase_idem]
  ring

/-- Expected diagonal second differences vanish. -/
theorem finiteBernoulliExpectation_traceSecondDifference_self (E : Finset ι) (p : ℝ)
    (e : ι) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (traceSecondDifference e e X) = 0 := by
  have h : finiteBernoulliExpectation E p (traceSecondDifference e e X) =
      finiteBernoulliExpectation E p (fun _ => (0 : ℝ)) :=
    finiteBernoulliExpectation_congr fun s _ => traceSecondDifference_self e X s
  rw [h, finiteBernoulliExpectation_const]

/-- **The second-derivative formula (2.33), double-sum form.** The derivative of `p ↦ E_p(X)`
(which is `∑_e E_p(δ_e X)` by Theorem 2.32) is itself differentiable, with derivative the
double sum `∑_e ∑_f E_p(δ_f δ_e X)`; hence `d²/dp² E_p(X) = ∑_e ∑_f E_p(δ_f δ_e X)`.
Grimmett's (2.33) is the series/parallel reading of this double sum for `X = 1_A`: after the
diagonal terms are dropped (`traceSecondDifference_self`), the summand for `f ≠ e` splits the
configurations by whether the pair `{e, f}` acts in series or in parallel for `A`. -/
theorem hasDerivAt_sum_finiteBernoulliExpectation_traceDifference {E : Finset ι}
    (X : Finset ι → ℝ) (p : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∑ e ∈ E, finiteBernoulliExpectation E x (traceDifference e X))
      (∑ e ∈ E, ∑ f ∈ E, finiteBernoulliExpectation E p (traceSecondDifference f e X))
      p :=
  HasDerivAt.fun_sum fun e _ => hasDerivAt_finiteBernoulliExpectation (traceDifference e X) p

/-- The second-derivative formula (2.33) with the vanishing diagonal removed:
`d²/dp² E_p(X) = ∑_e ∑_{f ≠ e} E_p(δ_f δ_e X)`. -/
theorem hasDerivAt_sum_finiteBernoulliExpectation_traceDifference_offDiag {E : Finset ι}
    (X : Finset ι → ℝ) (p : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∑ e ∈ E, finiteBernoulliExpectation E x (traceDifference e X))
      (∑ e ∈ E, ∑ f ∈ E.erase e,
        finiteBernoulliExpectation E p (traceSecondDifference f e X)) p := by
  have h := hasDerivAt_sum_finiteBernoulliExpectation_traceDifference (E := E) X p
  have hsum : ∀ e ∈ E,
      ∑ f ∈ E.erase e, finiteBernoulliExpectation E p (traceSecondDifference f e X) =
        ∑ f ∈ E, finiteBernoulliExpectation E p (traceSecondDifference f e X) := fun e _ =>
    Finset.sum_erase E
      (by rw [finiteBernoulliExpectation_traceSecondDifference_self])
  rw [Finset.sum_congr rfl hsum]
  exact h

/-- **The second-derivative formula (2.33) for events.** For an increasing trace event the
function differentiated here is the derivative of `p ↦ P_p(T)` (Russo), so this statement
reads `d²/dp² P_p(T) = ∑_e ∑_{f ≠ e} E_p(δ_f δ_e 1_T)` — Grimmett's (2.33) after the
series/parallel decomposition of the summands. -/
theorem hasDerivAt_sum_finiteBernoulliProbability_pivotalTrace {E : Finset ι}
    {T : Set (Finset ι)} (hT : IsIncreasingTrace T) (p : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e))
      (∑ e ∈ E, ∑ f ∈ E.erase e, finiteBernoulliExpectation E p
        (traceSecondDifference f e (T.indicator fun _ => (1 : ℝ)))) p := by
  have h := hasDerivAt_sum_finiteBernoulliExpectation_traceDifference_offDiag (E := E)
    (T.indicator fun _ => (1 : ℝ)) p
  have hfun : (fun x : ℝ => ∑ e ∈ E, finiteBernoulliExpectation E x
      (traceDifference e (T.indicator fun _ => (1 : ℝ)))) =
        fun x : ℝ => ∑ e ∈ E, finiteBernoulliProbability E x (pivotalTrace T e) :=
    funext fun x => Finset.sum_congr rfl fun e _ =>
      finiteBernoulliExpectation_congr fun s _ => hT.traceDifference_indicator e s
  rw [hfun] at h
  exact h

end Percolation
