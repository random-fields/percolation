import Percolation.Bernoulli.Basic
import Mathlib.Order.UpperLower.Basic

/-!
# Increasing events and finite supports

Source: Grimmett, *Percolation* (2nd ed., 1999), §2.1, pp. 32–33
(source id `grimmett-percolation-1999`).

Configurations of the abstract product space `Ω = ∏_{s ∈ S} {0,1}` are encoded as
`Set ι` (the set of open coordinates), ordered by inclusion, matching
`Percolation.EdgeConfiguration` for the cubic lattice. This file provides the purely
order-theoretic vocabulary of Chapter 2:

* `Percolation.IsIncreasingEvent`, `Percolation.IsDecreasingEvent` — Grimmett's increasing
  and decreasing events;
* `Percolation.IsIncreasingRandomVariable` — increasing random variables `N` with
  `N(ω) ≤ N(ω')` whenever `ω ≤ ω'`;
* `Percolation.DependsOn`, `Percolation.DependsOnFun` — events and observables defined in
  terms of the states of the coordinates in a finite set `E` only ("depending on finitely
  many edges");
* `Percolation.restrictTo`, `Percolation.spliceOn` — the finite trace of a configuration on
  a finite support and the splice replacing that trace, used by the finite-volume transfer
  lemmas of the following files.
-/

namespace Percolation

variable {ι : Type*}

/-- An event of the product space is *increasing* when opening further coordinates cannot
destroy it: `ω ≤ ω'` and `ω ∈ A` imply `ω' ∈ A` (Grimmett p. 32). -/
def IsIncreasingEvent (A : Set (Set ι)) : Prop :=
  ∀ ⦃ω η : Set ι⦄, ω ⊆ η → ω ∈ A → η ∈ A

/-- An event is *decreasing* when closing coordinates cannot destroy it (Grimmett p. 32). -/
def IsDecreasingEvent (A : Set (Set ι)) : Prop :=
  ∀ ⦃ω η : Set ι⦄, ω ⊆ η → η ∈ A → ω ∈ A

/-- A random variable on configurations is *increasing* when it is monotone for the
coordinatewise order (Grimmett p. 33). -/
def IsIncreasingRandomVariable {α : Type*} [Preorder α] (N : Set ι → α) : Prop :=
  ∀ ⦃ω η : Set ι⦄, ω ⊆ η → N ω ≤ N η

/-- A random variable is *decreasing* when it is antitone for the coordinatewise order. -/
def IsDecreasingRandomVariable {α : Type*} [Preorder α] (N : Set ι → α) : Prop :=
  ∀ ⦃ω η : Set ι⦄, ω ⊆ η → N η ≤ N ω

theorem IsIncreasingEvent.mono {A : Set (Set ι)} (hA : IsIncreasingEvent A)
    {ω η : Set ι} (hωη : ω ⊆ η) (hω : ω ∈ A) : η ∈ A :=
  hA hωη hω

theorem IsDecreasingEvent.mono {A : Set (Set ι)} (hA : IsDecreasingEvent A)
    {ω η : Set ι} (hωη : ω ⊆ η) (hη : η ∈ A) : ω ∈ A :=
  hA hωη hη

theorem isIncreasingEvent_iff_isUpperSet {A : Set (Set ι)} :
    IsIncreasingEvent A ↔ IsUpperSet A :=
  Iff.rfl

theorem isDecreasingEvent_iff_isLowerSet {A : Set (Set ι)} :
    IsDecreasingEvent A ↔ IsLowerSet A := by
  constructor
  · intro hA ω η hηω hω
    exact hA hηω hω
  · intro hA ω η hωη hη
    exact hA hωη hη

/-- Grimmett's definition of decreasing: the complement is increasing. -/
theorem isDecreasingEvent_iff_isIncreasingEvent_compl {A : Set (Set ι)} :
    IsDecreasingEvent A ↔ IsIncreasingEvent Aᶜ := by
  constructor
  · intro hA ω η hωη hω hη
    exact hω (hA hωη hη)
  · intro hA ω η hωη hη
    by_contra hω
    exact hA hωη hω hη

theorem IsIncreasingEvent.compl {A : Set (Set ι)} (hA : IsIncreasingEvent A) :
    IsDecreasingEvent Aᶜ := by
  intro ω η hωη hη hω
  exact hη (hA hωη hω)

theorem IsDecreasingEvent.compl {A : Set (Set ι)} (hA : IsDecreasingEvent A) :
    IsIncreasingEvent Aᶜ :=
  isDecreasingEvent_iff_isIncreasingEvent_compl.mp hA

theorem IsIncreasingEvent.inter {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    IsIncreasingEvent (A ∩ B) :=
  fun _ _ hωη hω => ⟨hA hωη hω.1, hB hωη hω.2⟩

theorem IsIncreasingEvent.union {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    IsIncreasingEvent (A ∪ B) :=
  fun _ _ hωη hω => hω.imp (hA hωη) (hB hωη)

theorem isIncreasingEvent_iInter {κ : Sort*} {A : κ → Set (Set ι)}
    (hA : ∀ k, IsIncreasingEvent (A k)) : IsIncreasingEvent (⋂ k, A k) := by
  intro ω η hωη hω
  simp only [Set.mem_iInter] at hω ⊢
  exact fun k => hA k hωη (hω k)

theorem isIncreasingEvent_iUnion {κ : Sort*} {A : κ → Set (Set ι)}
    (hA : ∀ k, IsIncreasingEvent (A k)) : IsIncreasingEvent (⋃ k, A k) := by
  intro ω η hωη hω
  simp only [Set.mem_iUnion] at hω ⊢
  exact hω.imp fun k hk => hA k hωη hk

theorem IsDecreasingEvent.inter {A B : Set (Set ι)}
    (hA : IsDecreasingEvent A) (hB : IsDecreasingEvent B) :
    IsDecreasingEvent (A ∩ B) :=
  fun _ _ hωη hη => ⟨hA hωη hη.1, hB hωη hη.2⟩

theorem IsDecreasingEvent.union {A B : Set (Set ι)}
    (hA : IsDecreasingEvent A) (hB : IsDecreasingEvent B) :
    IsDecreasingEvent (A ∪ B) :=
  fun _ _ hωη hη => hη.imp (hA hωη) (hB hωη)

theorem isIncreasingEvent_empty : IsIncreasingEvent (∅ : Set (Set ι)) :=
  fun _ _ _ hω => hω.elim

theorem isIncreasingEvent_univ : IsIncreasingEvent (Set.univ : Set (Set ι)) :=
  fun _ _ _ _ => Set.mem_univ _

/-- The event that every coordinate of a fixed set is open is increasing. -/
theorem isIncreasingEvent_superset (s : Set ι) :
    IsIncreasingEvent {ω : Set ι | s ⊆ ω} :=
  fun _ _ hωη hω => hω.trans hωη

theorem IsIncreasingRandomVariable.mono {α : Type*} [Preorder α] {N : Set ι → α}
    (hN : IsIncreasingRandomVariable N) {ω η : Set ι} (hωη : ω ⊆ η) : N ω ≤ N η :=
  hN hωη

theorem isIncreasingRandomVariable_iff_monotone {α : Type*} [Preorder α] {N : Set ι → α} :
    IsIncreasingRandomVariable N ↔ Monotone N :=
  Iff.rfl

/-- An event is increasing exactly when its real indicator function is an increasing random
variable (Grimmett p. 33). -/
theorem isIncreasingEvent_iff_indicator_isIncreasingRandomVariable {A : Set (Set ι)} :
    IsIncreasingEvent A ↔
      IsIncreasingRandomVariable (A.indicator fun _ => (1 : ℝ)) := by
  constructor
  · intro hA ω η hωη
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hA hωη hω)]
    · rw [Set.indicator_of_notMem hω]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  · intro hind ω η hωη hω
    by_contra hη
    have := hind hωη
    rw [Set.indicator_of_mem hω, Set.indicator_of_notMem hη] at this
    exact absurd this (by norm_num)

theorem IsIncreasingEvent.indicator_isIncreasingRandomVariable {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) :
    IsIncreasingRandomVariable (A.indicator fun _ => (1 : ℝ)) :=
  isIncreasingEvent_iff_indicator_isIncreasingRandomVariable.mp hA

/-! ### Finite supports -/

/-- An event *depends on* the finite coordinate set `E` when membership is determined by the
states of the coordinates in `E` (Grimmett's "defined in terms of the states of only
finitely many edges"). -/
def DependsOn (E : Finset ι) (A : Set (Set ι)) : Prop :=
  ∀ ⦃ω η : Set ι⦄, (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) → (ω ∈ A ↔ η ∈ A)

/-- An observable *depends on* the finite coordinate set `E` when its value is determined by
the states of the coordinates in `E`. -/
def DependsOnFun {α : Type*} (E : Finset ι) (X : Set ι → α) : Prop :=
  ∀ ⦃ω η : Set ι⦄, (∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) → X ω = X η

theorem DependsOn.congr {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A)
    {ω η : Set ι} (h : ∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) : ω ∈ A ↔ η ∈ A :=
  hA h

theorem DependsOn.mono {E F : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A)
    (hEF : E ⊆ F) : DependsOn F A :=
  fun _ _ h => hA fun e he => h e (hEF he)

theorem DependsOn.inter {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) : DependsOn E (A ∩ B) :=
  fun _ _ h => and_congr (hA h) (hB h)

theorem DependsOn.union {E : Finset ι} {A B : Set (Set ι)}
    (hA : DependsOn E A) (hB : DependsOn E B) : DependsOn E (A ∪ B) :=
  fun _ _ h => or_congr (hA h) (hB h)

theorem DependsOn.compl {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) :
    DependsOn E Aᶜ :=
  fun _ _ h => not_congr (hA h)

theorem dependsOn_empty_iff {A : Set (Set ι)} :
    DependsOn (∅ : Finset ι) A ↔ A = ∅ ∨ A = Set.univ := by
  constructor
  · intro hA
    rcases Set.eq_empty_or_nonempty A with hA0 | ⟨ω, hω⟩
    · exact Or.inl hA0
    · refine Or.inr (Set.eq_univ_of_forall fun η => ?_)
      exact (hA fun e he => absurd he (Finset.notMem_empty e)).mp hω
  · rintro (rfl | rfl)
    · exact fun _ _ _ => Iff.rfl
    · exact fun _ _ _ => Iff.rfl

theorem dependsOn_univ (E : Finset ι) : DependsOn E (Set.univ : Set (Set ι)) :=
  fun _ _ _ => Iff.rfl

theorem dependsOn_empty_event (E : Finset ι) : DependsOn E (∅ : Set (Set ι)) :=
  fun _ _ _ => Iff.rfl

theorem DependsOnFun.congr {α : Type*} {E : Finset ι} {X : Set ι → α}
    (hX : DependsOnFun E X) {ω η : Set ι} (h : ∀ e ∈ E, (e ∈ ω ↔ e ∈ η)) : X ω = X η :=
  hX h

theorem DependsOnFun.mono {α : Type*} {E F : Finset ι} {X : Set ι → α}
    (hX : DependsOnFun E X) (hEF : E ⊆ F) : DependsOnFun F X :=
  fun _ _ h => hX fun e he => h e (hEF he)

/-- The event that all coordinates of `s` are open depends on `s`. -/
theorem dependsOn_superset (s : Finset ι) :
    DependsOn s {ω : Set ι | (s : Set ι) ⊆ ω} := by
  intro ω η h
  constructor
  · intro hω e he
    exact (h e he).mp (hω he)
  · intro hη e he
    exact (h e he).mpr (hη he)

/-- An event depending on `E` corresponds to a predicate on indicator functions restricted to
`E`; membership is invariant under replacing a configuration by its trace on `E`
(`DependsOn.mem_iff_restrictTo_mem` below makes this precise). -/
theorem DependsOn.indicator_dependsOnFun {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) :
    DependsOnFun E (A.indicator fun _ => (1 : ℝ)) := by
  intro ω η h
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem ((hA h).mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem fun hη => hω ((hA h).mpr hη)]

/-! ### Traces and splices on a finite support -/

/-- The trace of a configuration on the finite support `E`: the finite set of open
coordinates inside `E`. -/
noncomputable def restrictTo (E : Finset ι) (ω : Set ι) : Finset ι :=
  letI := Classical.decPred fun e : ι => e ∈ ω
  E.filter fun e => e ∈ ω

@[simp] theorem mem_restrictTo {E : Finset ι} {ω : Set ι} {e : ι} :
    e ∈ restrictTo E ω ↔ e ∈ E ∧ e ∈ ω := by
  classical
  simp [restrictTo]

theorem restrictTo_subset (E : Finset ι) (ω : Set ι) : restrictTo E ω ⊆ E :=
  fun _ he => (mem_restrictTo.mp he).1

theorem restrictTo_mono {E : Finset ι} {ω η : Set ι} (hωη : ω ⊆ η) :
    restrictTo E ω ⊆ restrictTo E η := by
  intro e he
  rw [mem_restrictTo] at he ⊢
  exact ⟨he.1, hωη he.2⟩

theorem restrictTo_coe (E s : Finset ι) (hs : s ⊆ E) :
    restrictTo E (↑s : Set ι) = s := by
  ext e
  rw [mem_restrictTo]
  exact ⟨fun h => by simpa using h.2, fun h => ⟨hs h, by simpa using h⟩⟩

/-- Replace the trace of `ω` on the support `E` by the finite set `s`. -/
def spliceOn (E s : Finset ι) (ω : Set ι) : Set ι :=
  ↑s ∪ (ω \ ↑E)

theorem mem_spliceOn {E s : Finset ι} {ω : Set ι} {e : ι} :
    e ∈ spliceOn E s ω ↔ e ∈ s ∨ (e ∈ ω ∧ e ∉ E) := by
  simp [spliceOn]

/-- Inside the support, the splice is exactly `s`. -/
theorem mem_spliceOn_of_mem {E s : Finset ι} {ω : Set ι} {e : ι}
    (he : e ∈ E) : e ∈ spliceOn E s ω ↔ e ∈ s := by
  rw [mem_spliceOn]
  exact ⟨fun h => h.elim id fun h' => absurd he h'.2, Or.inl⟩

/-- Outside the support, the splice agrees with the original configuration. -/
theorem mem_spliceOn_of_notMem {E s : Finset ι} (hs : s ⊆ E) {ω : Set ι} {e : ι}
    (he : e ∉ E) : e ∈ spliceOn E s ω ↔ e ∈ ω := by
  rw [mem_spliceOn]
  exact ⟨fun h => h.elim (fun h' => absurd (hs h') he) And.left, fun h => Or.inr ⟨h, he⟩⟩

@[simp] theorem spliceOn_restrictTo_self (E : Finset ι) (ω : Set ι) :
    spliceOn E (restrictTo E ω) ω = ω := by
  ext e
  rw [mem_spliceOn, mem_restrictTo]
  by_cases he : e ∈ E <;> tauto

theorem spliceOn_mono_left {E s t : Finset ι} (hst : s ⊆ t) (ω : Set ι) :
    spliceOn E s ω ⊆ spliceOn E t ω :=
  Set.union_subset_union_left _ (Finset.coe_subset.mpr hst)

theorem spliceOn_mono_right (E s : Finset ι) {ω η : Set ι} (hωη : ω ⊆ η) :
    spliceOn E s ω ⊆ spliceOn E s η :=
  Set.union_subset_union_right _ (Set.diff_subset_diff_left hωη)

/-- Membership of an event with support `E` is read off the trace on `E`. -/
theorem DependsOn.mem_iff_restrictTo_mem {E : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (ω : Set ι) :
    ω ∈ A ↔ (↑(restrictTo E ω) : Set ι) ∈ A := by
  refine hA fun e he => ?_
  simp [mem_restrictTo, he]

/-- Membership of an event with support `E` is invariant under splicing an arbitrary trace:
the spliced configuration lies in `A` iff the trace itself (as a configuration) does. -/
theorem DependsOn.spliceOn_mem_iff {E s : Finset ι} {A : Set (Set ι)}
    (hA : DependsOn E A) (ω : Set ι) :
    spliceOn E s ω ∈ A ↔ (↑s : Set ι) ∈ A := by
  refine hA fun e he => ?_
  rw [mem_spliceOn_of_mem he]
  simp

end Percolation
