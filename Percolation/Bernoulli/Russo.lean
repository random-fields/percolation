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

/-- Force a finite-cube coordinate open. This is the finite trace analogue of `forceOpen`. -/
def finiteForceOpen {ι : Type*} [DecidableEq ι] (e : ι) (s : Finset ι) : Finset ι :=
  insert e s

/-- Force a finite-cube coordinate closed. This is the finite trace analogue of `forceClosed`. -/
def finiteForceClosed {ι : Type*} [DecidableEq ι] (e : ι) (s : Finset ι) : Finset ι :=
  s.erase e

@[simp]
theorem finiteForceOpen_eq_self {ι : Type*} [DecidableEq ι]
    {e : ι} {s : Finset ι} (he : e ∈ s) :
    finiteForceOpen e s = s := by
  exact Finset.insert_eq_of_mem he

@[simp]
theorem finiteForceClosed_eq_self {ι : Type*} [DecidableEq ι]
    {e : ι} {s : Finset ι} (he : e ∉ s) :
    finiteForceClosed e s = s := by
  simp [finiteForceClosed, he]

/-- Coordinate `e` is pivotal for a finite trace if opening `e` puts the trace in the event and
closing `e` removes it. -/
def IsPivotalTrace {ι : Type*} [DecidableEq ι]
    (T : Set (Finset ι)) (e : ι) (s : Finset ι) : Prop :=
  finiteForceOpen e s ∈ T ∧ finiteForceClosed e s ∉ T

theorem finset_insert_erase_eq_insert {ι : Type*} [DecidableEq ι] (e : ι) (s : Finset ι) :
    insert e (s.erase e) = insert e s := by
  ext f
  by_cases hfe : f = e
  · subst f
    simp
  · simp [hfe]

/-- Finite pivotality is unchanged by forcing the pivotal coordinate open. -/
theorem isPivotalTrace_insert {ι : Type*} [DecidableEq ι]
    (T : Set (Finset ι)) (e : ι) (s : Finset ι) :
    IsPivotalTrace T e (insert e s) ↔ IsPivotalTrace T e s := by
  simp [IsPivotalTrace, finiteForceOpen, finiteForceClosed]

/-- Finite pivotality is unchanged by forcing the pivotal coordinate closed. -/
theorem isPivotalTrace_erase {ι : Type*} [DecidableEq ι]
    (T : Set (Finset ι)) (e : ι) (s : Finset ι) :
    IsPivotalTrace T e (s.erase e) ↔ IsPivotalTrace T e s := by
  simp [IsPivotalTrace, finiteForceOpen, finiteForceClosed, finset_insert_erase_eq_insert]

/-- Finite trace version of the set identity behind Grimmett's equation (2.29):
open-and-pivotal equals event-and-pivotal. -/
theorem open_inter_pivotalTrace_eq_event_inter_pivotalTrace {ι : Type*} [DecidableEq ι]
    (T : Set (Finset ι)) (e : ι) :
    ({s : Finset ι | e ∈ s} ∩ {s : Finset ι | IsPivotalTrace T e s}) =
      (T ∩ {s : Finset ι | IsPivotalTrace T e s}) := by
  ext s
  constructor
  · rintro ⟨he, hpiv⟩
    exact ⟨by simpa [finiteForceOpen_eq_self he] using hpiv.1, hpiv⟩
  · rintro ⟨hT, hpiv⟩
    by_cases he : e ∈ s
    · exact ⟨he, hpiv⟩
    · have hclosed : finiteForceClosed e s = s := finiteForceClosed_eq_self he
      exact (hpiv.2 (by simpa [hclosed] using hT)).elim

/-- If a finite event is invariant under opening a fresh coordinate, then its probability on
the enlarged support agrees with its probability on the old support. -/
theorem finiteBernoulliEventProbability_insert_invariant {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {e : ι} (he : e ∉ E) (p : ℝ) (P : Set (Finset ι))
    (hP : ∀ ⦃s : Finset ι⦄, s ⊆ E → (insert e s ∈ P ↔ s ∈ P)) :
    finiteBernoulliEventProbability (insert e E) p P =
      finiteBernoulliEventProbability E p P := by
  unfold finiteBernoulliEventProbability
  rw [finiteBernoulliExpectation_insert he]
  apply finiteBernoulliExpectation_congr
  intro s hsE
  by_cases hs : s ∈ P
  · have hsins : insert e s ∈ P := (hP hsE).2 hs
    simp [Set.indicator_of_mem hs, Set.indicator_of_mem hsins,
      twoPointBernoulliExpectation_const]
  · have hsins : insert e s ∉ P := by
      intro h
      exact hs ((hP hsE).1 h)
    simp [Set.indicator_of_notMem hs, Set.indicator_of_notMem hsins,
      twoPointBernoulliExpectation_const]

/-- If a finite event is invariant under opening a fresh coordinate, then intersecting it with
the event that the fresh coordinate is open multiplies its probability by `p`. -/
theorem finiteBernoulliEventProbability_insert_open_invariant {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {e : ι} (he : e ∉ E) (p : ℝ)
    (P : Set (Finset ι))
    (hP : ∀ ⦃s : Finset ι⦄, s ⊆ E → (insert e s ∈ P ↔ s ∈ P)) :
    finiteBernoulliEventProbability (insert e E) p ({s | e ∈ s} ∩ P) =
      p * finiteBernoulliEventProbability E p P := by
  unfold finiteBernoulliEventProbability
  rw [finiteBernoulliExpectation_insert he]
  rw [← finiteBernoulliExpectation_const_mul E p p
    (fun s ↦ P.indicator (fun _ ↦ (1 : ℝ)) s)]
  apply finiteBernoulliExpectation_congr
  intro s hsE
  have hnot : e ∉ s := Finset.notMem_mono hsE he
  by_cases hs : s ∈ P
  · have hsins : insert e s ∈ P := (hP hsE).2 hs
    simp [hnot, hs, hsins, twoPointBernoulliExpectation_zero_left]
  · have hsins : insert e s ∉ P := by
      intro h
      exact hs ((hP hsE).1 h)
    simp [hnot, hs, hsins, twoPointBernoulliExpectation_zero_left]

/-- Finite-cube independence form of Grimmett's observation before equation (2.29): the pivotal
event ignores the state of `e`, so open-and-pivotal has probability `p` times pivotal. -/
theorem finiteBernoulliEventProbability_open_pivotalTrace_eq_mul {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {e : ι} (he : e ∉ E) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliEventProbability (insert e E) p
        ({s : Finset ι | e ∈ s} ∩ {s : Finset ι | IsPivotalTrace T e s}) =
      p * finiteBernoulliEventProbability (insert e E) p
        {s : Finset ι | IsPivotalTrace T e s} := by
  let P : Set (Finset ι) := {s | IsPivotalTrace T e s}
  have hP : ∀ ⦃s : Finset ι⦄, s ⊆ E → (insert e s ∈ P ↔ s ∈ P) := by
    intro s _hsE
    exact isPivotalTrace_insert T e s
  rw [finiteBernoulliEventProbability_insert_open_invariant he p P hP]
  rw [finiteBernoulliEventProbability_insert_invariant he p P hP]

/-- Finite-cube equation (2.29) input: event-and-pivotal has probability `p` times pivotal. -/
theorem finiteBernoulliEventProbability_event_inter_pivotalTrace_eq_mul {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {e : ι} (he : e ∉ E) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliEventProbability (insert e E) p
        (T ∩ {s : Finset ι | IsPivotalTrace T e s}) =
      p * finiteBernoulliEventProbability (insert e E) p
        {s : Finset ι | IsPivotalTrace T e s} := by
  rw [← open_inter_pivotalTrace_eq_event_inter_pivotalTrace T e]
  exact finiteBernoulliEventProbability_open_pivotalTrace_eq_mul he p T

end Percolation
