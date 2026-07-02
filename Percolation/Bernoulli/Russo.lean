import Percolation.Bernoulli.Increasing

/-!
# Pivotal edges for Russo's formula

This file adds the deterministic event-level definitions used in Grimmett's Russo formula
(Theorem 2.25): force an edge open or closed, define pivotality, and show that the event
"`e` is pivotal" depends on all relevant coordinates except the state of `e` itself.
-/

namespace Percolation

/-- Force coordinate `e` to be open. -/
def forceOpen {ι : Type*} (e : ι) (ω : Set ι) : Set ι :=
  insert e ω

/-- Force coordinate `e` to be closed. -/
def forceClosed {ι : Type*} (e : ι) (ω : Set ι) : Set ι :=
  ω \ {e}

@[simp]
theorem mem_forceOpen_iff {ι : Type*} (e f : ι) (ω : Set ι) :
    f ∈ forceOpen e ω ↔ f = e ∨ f ∈ ω := by
  simp [forceOpen]

@[simp]
theorem mem_forceClosed_iff {ι : Type*} (e f : ι) (ω : Set ι) :
    f ∈ forceClosed e ω ↔ f ∈ ω ∧ f ≠ e := by
  simp [forceClosed]

@[simp]
theorem self_mem_forceOpen {ι : Type*} (e : ι) (ω : Set ι) :
    e ∈ forceOpen e ω := by
  simp [forceOpen]

@[simp]
theorem self_notMem_forceClosed {ι : Type*} (e : ι) (ω : Set ι) :
    e ∉ forceClosed e ω := by
  simp [forceClosed]

@[simp]
theorem forceOpen_eq_self {ι : Type*} {e : ι} {ω : Set ι} (he : e ∈ ω) :
    forceOpen e ω = ω := by
  exact Set.insert_eq_of_mem he

@[simp]
theorem forceClosed_eq_self {ι : Type*} {e : ι} {ω : Set ι} (he : e ∉ ω) :
    forceClosed e ω = ω := by
  ext f
  by_cases hfe : f = e
  · subst f
    simp [forceClosed, he]
  · simp [forceClosed, hfe]

/-- Coordinate `e` is pivotal for event `A` in configuration `ω` if opening `e` makes `A`
occur and closing `e` makes `A` fail. For increasing events this is Grimmett's pivotal edge. -/
def IsPivotal {ι : Type*} (A : Set (Set ι)) (e : ι) (ω : Set ι) : Prop :=
  forceOpen e ω ∈ A ∧ forceClosed e ω ∉ A

@[simp]
theorem isPivotal_iff {ι : Type*} (A : Set (Set ι)) (e : ι) (ω : Set ι) :
    IsPivotal A e ω ↔ forceOpen e ω ∈ A ∧ forceClosed e ω ∉ A :=
  Iff.rfl

/-- The pivotal coordinates in a finite support. -/
noncomputable def pivotalSet {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (A : Set (Set ι)) (ω : Set ι) : Finset ι := by
  classical
  exact E.filter fun e ↦ IsPivotal A e ω

/-- The number of pivotal coordinates in a finite support. -/
noncomputable def pivotalCount {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (A : Set (Set ι)) (ω : Set ι) : ℕ :=
  (pivotalSet E A ω).card

@[simp]
theorem mem_pivotalSet_iff {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (A : Set (Set ι)) (ω : Set ι) (e : ι) :
    e ∈ pivotalSet E A ω ↔ e ∈ E ∧ IsPivotal A e ω := by
  classical
  simp [pivotalSet]

theorem mem_of_isPivotal_of_mem {ι : Type*} {A : Set (Set ι)}
    {e : ι} {ω : Set ι} (hpiv : IsPivotal A e ω) (he : e ∈ ω) :
    ω ∈ A := by
  simpa [forceOpen_eq_self he] using hpiv.1

theorem notMem_of_isPivotal_of_notMem {ι : Type*} {A : Set (Set ι)}
    {e : ι} {ω : Set ι} (hpiv : IsPivotal A e ω) (he : e ∉ ω) :
    ω ∉ A := by
  simpa [forceClosed_eq_self he] using hpiv.2

/-- The event that `e` is open and pivotal agrees with `A ∩ {e pivotal}`. This is the set-level
identity behind Grimmett's equation (2.29). -/
theorem open_inter_pivotalEvent_eq_event_inter_pivotalEvent {ι : Type*}
    (A : Set (Set ι)) (e : ι) :
    ({ω : Set ι | e ∈ ω} ∩ {ω : Set ι | IsPivotal A e ω}) =
      (A ∩ {ω : Set ι | IsPivotal A e ω}) := by
  ext ω
  constructor
  · rintro ⟨he, hpiv⟩
    exact ⟨mem_of_isPivotal_of_mem hpiv he, hpiv⟩
  · rintro ⟨hA, hpiv⟩
    by_cases he : e ∈ ω
    · exact ⟨he, hpiv⟩
    · exact (notMem_of_isPivotal_of_notMem hpiv he hA).elim

/-- Configurations agree away from coordinate `e`. -/
def AgreeExcept {ι : Type*} (e : ι) (ω η : Set ι) : Prop :=
  ∀ f, f ≠ e → (f ∈ ω ↔ f ∈ η)

theorem forceOpen_eq_of_agreeExcept {ι : Type*} {e : ι} {ω η : Set ι}
    (h : AgreeExcept e ω η) :
    forceOpen e ω = forceOpen e η := by
  ext f
  by_cases hfe : f = e
  · subst f
    simp
  · simp [forceOpen, hfe, h f hfe]

theorem forceClosed_eq_of_agreeExcept {ι : Type*} {e : ι} {ω η : Set ι}
    (h : AgreeExcept e ω η) :
    forceClosed e ω = forceClosed e η := by
  ext f
  by_cases hfe : f = e
  · subst f
    simp
  · simp [forceClosed, hfe, h f hfe]

theorem isPivotal_congr_agreeExcept {ι : Type*} {A : Set (Set ι)}
    {e : ι} {ω η : Set ι} (h : AgreeExcept e ω η) :
    IsPivotal A e ω ↔ IsPivotal A e η := by
  rw [IsPivotal, IsPivotal, forceOpen_eq_of_agreeExcept h,
    forceClosed_eq_of_agreeExcept h]

theorem dependsOn_pivotalEvent {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} {e : ι}
    (hA : DependsOn E A) :
    DependsOn (E.erase e) {ω : Set ι | IsPivotal A e ω} := by
  intro ω η hcoord
  have hopen :
      (forceOpen e ω ∈ A ↔ forceOpen e η ∈ A) := by
    apply hA
    intro f hfE
    by_cases hfe : f = e
    · subst f
      simp [forceOpen]
    · have hfErase : f ∈ E.erase e := by
        simp [hfE, hfe]
      simpa [forceOpen, hfe] using hcoord f hfErase
  have hclosed :
      (forceClosed e ω ∈ A ↔ forceClosed e η ∈ A) := by
    apply hA
    intro f hfE
    by_cases hfe : f = e
    · subst f
      simp [forceClosed]
    · have hfErase : f ∈ E.erase e := by
        simp [hfE, hfe]
      simpa [forceClosed, hfe] using hcoord f hfErase
  exact and_congr hopen (not_congr hclosed)

end Percolation
