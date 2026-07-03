import Percolation.Bernoulli.Increasing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Pivotal edges for Russo's formula

This file adds the deterministic event-level definitions used in Grimmett's Russo formula
(Theorem 2.25): force an edge open or closed, define pivotality, and show that the event
"`e` is pivotal" depends on all relevant coordinates except the state of `e` itself.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset unitInterval BigOperators symmDiff

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

/-- The finite trace of the event-level pivotal event is exactly the finite-cube pivotal trace,
provided the pivotal coordinate belongs to the ambient finite support. -/
theorem eventTrace_pivotalEvent_eq {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} {e : ι} (he : e ∈ E) :
    (eventTrace E {ω : Set ι | IsPivotal A e ω} : Set (Finset ι)) =
      {s : Finset ι | IsPivotalTrace (eventTrace E A : Set (Finset ι)) e s} := by
  ext s
  change s ∈ eventTrace E {ω : Set ι | IsPivotal A e ω} ↔
    IsPivotalTrace (eventTrace E A : Set (Finset ι)) e s
  rw [mem_eventTrace_iff]
  constructor
  · rintro ⟨hsE, hpiv⟩
    change IsPivotal A e ((s : Finset ι) : Set ι) at hpiv
    constructor
    · change finiteForceOpen e s ∈ eventTrace E A
      rw [mem_eventTrace_iff]
      refine ⟨?_, ?_⟩
      · intro f hf
        have hf' : f = e ∨ f ∈ s := by simpa [finiteForceOpen] using hf
        exact hf'.elim (fun hfe ↦ by simpa [hfe] using he) (fun hfs ↦ hsE hfs)
      · simpa [finiteForceOpen, forceOpen] using hpiv.1
    · intro hclosed
      change finiteForceClosed e s ∈ eventTrace E A at hclosed
      have hclosedA : ((finiteForceClosed e s : Finset ι) : Set ι) ∈ A :=
        ((mem_eventTrace_iff E A (finiteForceClosed e s)).mp hclosed).2
      exact hpiv.2 (by simpa [finiteForceClosed, forceClosed] using hclosedA)
  · intro hpiv
    have hopen := (mem_eventTrace_iff E A (finiteForceOpen e s)).mp hpiv.1
    have hsE : s ⊆ E := by
      intro f hfs
      have hfopen : f ∈ finiteForceOpen e s := by
        simp [finiteForceOpen, hfs]
      exact hopen.1 hfopen
    refine ⟨hsE, ?_⟩
    change IsPivotal A e ((s : Finset ι) : Set ι)
    constructor
    · simpa [finiteForceOpen, forceOpen] using hopen.2
    · intro hclosedA
      apply hpiv.2
      change finiteForceClosed e s ∈ eventTrace E A
      rw [mem_eventTrace_iff]
      refine ⟨?_, ?_⟩
      · intro f hf
        have hf' : f ≠ e ∧ f ∈ s := by simpa [finiteForceClosed] using hf
        exact hsE hf'.2
      · simpa [finiteForceClosed, forceClosed] using hclosedA

/-- Product-measure probability of an event-level pivotal event agrees with the finite pivotal
trace probability for any event depending on the finite support. -/
theorem DependsOn.setBernoulli_real_pivotal_eq_finiteBernoulliEventProbability {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A)
    {e : ι} (he : e ∈ E) (p : I) :
    setBer((Set.univ : Set ι), p).real {ω : Set ι | IsPivotal A e ω} =
      finiteBernoulliEventProbability E (p : ℝ)
        {s : Finset ι | IsPivotalTrace (eventTrace E A : Set (Finset ι)) e s} := by
  have hpivDep : DependsOn E {ω : Set ι | IsPivotal A e ω} :=
    (dependsOn_pivotalEvent (E := E) (A := A) (e := e) hA).mono
      (Finset.erase_subset e E)
  rw [hpivDep.setBernoulli_real_eq_finiteBernoulliEventProbability p]
  rw [eventTrace_pivotalEvent_eq (E := E) (A := A) he]

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

/-- For an increasing finite trace, the difference between the indicators with `e` forced open
and closed is exactly the pivotal indicator. This is the pointwise identity behind Grimmett's
finite-coordinate Russo difference computation. -/
theorem indicator_insert_sub_eq_pivotalTrace {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {e : ι} (he : e ∉ E) {T : Set (Finset ι)}
    (hT : IsIncreasingTrace (insert e E) T) {s : Finset ι} (hsE : s ⊆ E) :
    T.indicator (fun _ ↦ (1 : ℝ)) (insert e s) - T.indicator (fun _ ↦ (1 : ℝ)) s =
      ({u : Finset ι | IsPivotalTrace T e u}).indicator (fun _ ↦ (1 : ℝ)) s := by
  have hnot : e ∉ s := Finset.notMem_mono hsE he
  have hclosed : finiteForceClosed e s = s := finiteForceClosed_eq_self hnot
  have hopen : finiteForceOpen e s = insert e s := rfl
  by_cases hs : s ∈ T
  · have hins : insert e s ∈ T := by
      exact hT (by intro x hx; exact Finset.mem_insert.mpr (Or.inr hx))
        (Finset.insert_subset_insert e hsE) hs
    have hnotpiv : ¬ IsPivotalTrace T e s := by
      intro hpiv
      exact hpiv.2 (by simpa [hclosed] using hs)
    simp [hs, hins, hnotpiv]
  · by_cases hins : insert e s ∈ T
    · have hpiv : IsPivotalTrace T e s := by
        simpa [IsPivotalTrace, hopen, hclosed] using And.intro hins hs
      simp [hs, hins, hpiv]
    · have hnotpiv : ¬ IsPivotalTrace T e s := by
        intro hpiv
        exact hins (by simpa [hopen] using hpiv.1)
      simp [hs, hins, hnotpiv]

/-- Finite heterogeneous one-coordinate Russo identity. If the two product measures differ only
in the fresh coordinate `e`, then changing the probability of `e` changes the probability of an
increasing trace by `(r e - q e)` times the pivotal probability. This is the finite algebraic
step in Grimmett's proof of Theorem (2.25). -/
theorem finiteBernoulliHeteroEventProbability_single_coordinate_difference {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {e : ι} (he : e ∉ E) {q r : ι → ℝ}
    {T : Set (Finset ι)} (hqr : ∀ f ∈ E, r f = q f)
    (hT : IsIncreasingTrace (insert e E) T) :
    finiteBernoulliHeteroEventProbability (insert e E) r T -
        finiteBernoulliHeteroEventProbability (insert e E) q T =
      (r e - q e) * finiteBernoulliHeteroEventProbability (insert e E) q
        {s : Finset ι | IsPivotalTrace T e s} := by
  let P : Set (Finset ι) := {s | IsPivotalTrace T e s}
  have hP : ∀ ⦃s : Finset ι⦄, s ⊆ E → (insert e s ∈ P ↔ s ∈ P) := by
    intro s _hsE
    exact isPivotalTrace_insert T e s
  rw [show finiteBernoulliHeteroEventProbability (insert e E) r T =
      finiteBernoulliHeteroExpectation E q
        (fun s ↦ (1 - r e) * T.indicator (fun _ ↦ (1 : ℝ)) s +
          r e * T.indicator (fun _ ↦ (1 : ℝ)) (insert e s)) by
    unfold finiteBernoulliHeteroEventProbability
    rw [finiteBernoulliHeteroExpectation_insert he]
    exact finiteBernoulliHeteroExpectation_congr hqr (fun _s _hsE ↦ rfl)]
  rw [show finiteBernoulliHeteroEventProbability (insert e E) q T =
      finiteBernoulliHeteroExpectation E q
        (fun s ↦ (1 - q e) * T.indicator (fun _ ↦ (1 : ℝ)) s +
          q e * T.indicator (fun _ ↦ (1 : ℝ)) (insert e s)) by
    unfold finiteBernoulliHeteroEventProbability
    rw [finiteBernoulliHeteroExpectation_insert he]]
  rw [show finiteBernoulliHeteroEventProbability (insert e E) q P =
      finiteBernoulliHeteroEventProbability E q P by
    exact finiteBernoulliHeteroEventProbability_insert_invariant he q P hP]
  unfold finiteBernoulliHeteroEventProbability
  unfold finiteBernoulliHeteroExpectation
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  have hdiff := indicator_insert_sub_eq_pivotalTrace he hT hsE
  have hdiffP :
      T.indicator (fun _ ↦ (1 : ℝ)) (insert e s) -
          T.indicator (fun _ ↦ (1 : ℝ)) s =
        P.indicator (fun _ ↦ (1 : ℝ)) s := by
    simpa [P] using hdiff
  simp only
  rw [← hdiffP]
  ring

/-- Partial-derivative form of the finite heterogeneous Russo identity. Varying only coordinate
`e`, at the current coordinate value, has derivative equal to the pivotal probability. This is the
coordinate derivative used before summing directions to obtain the usual finite uniform-parameter
Russo formula. -/
theorem finiteBernoulliHeteroEventProbability_hasDerivAt_update {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {e : ι} (he : e ∉ E) {q : ι → ℝ}
    {T : Set (Finset ι)} (hT : IsIncreasingTrace (insert e E) T) :
    HasDerivAt
      (fun x : ℝ ↦ finiteBernoulliHeteroEventProbability (insert e E)
        (Function.update q e x) T)
      (finiteBernoulliHeteroEventProbability (insert e E) q
        {s : Finset ι | IsPivotalTrace T e s})
      (q e) := by
  let piv : ℝ := finiteBernoulliHeteroEventProbability (insert e E) q
    {s : Finset ι | IsPivotalTrace T e s}
  have h_affine :
      (fun x : ℝ ↦ finiteBernoulliHeteroEventProbability (insert e E)
        (Function.update q e x) T) =
        (fun x : ℝ ↦ finiteBernoulliHeteroEventProbability (insert e E) q T +
          (x - q e) * piv) := by
    funext x
    have hqr : ∀ f ∈ E, Function.update q e x f = q f := by
      intro f hf
      have hfe : f ≠ e := by
        intro h
        exact he (by simpa [h] using hf)
      exact Function.update_of_ne hfe x q
    have hdiff :=
      finiteBernoulliHeteroEventProbability_single_coordinate_difference he hqr hT
    dsimp [piv]
    rw [Function.update_self] at hdiff
    nlinarith [hdiff]
  rw [h_affine]
  have hsub : HasDerivAt (fun x : ℝ ↦ x - q e) 1 (q e) := by
    exact (hasDerivAt_id (q e)).sub_const (q e)
  have hderiv : HasDerivAt
      (fun x : ℝ ↦ finiteBernoulliHeteroEventProbability (insert e E) q T +
        (x - q e) * piv) (1 * piv) (q e) := by
    simpa only [Pi.add_apply, zero_add] using
      HasDerivAt.add
        (hasDerivAt_const (q e) (finiteBernoulliHeteroEventProbability (insert e E) q T))
        (hsub.mul_const piv)
  simpa [piv] using hderiv

/-- Homogeneous-point corollary of the finite heterogeneous coordinate derivative. If all
coordinates currently have probability `p`, then varying only coordinate `e` has derivative equal
to the ordinary homogeneous pivotal probability. -/
theorem finiteBernoulliHeteroEventProbability_hasDerivAt_update_const {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {e : ι} (he : e ∉ E) (p : ℝ)
    {T : Set (Finset ι)} (hT : IsIncreasingTrace (insert e E) T) :
    HasDerivAt
      (fun x : ℝ ↦ finiteBernoulliHeteroEventProbability (insert e E)
        (Function.update (fun _ ↦ p) e x) T)
      (finiteBernoulliEventProbability (insert e E) p
        {s : Finset ι | IsPivotalTrace T e s})
      p := by
  have h := finiteBernoulliHeteroEventProbability_hasDerivAt_update
    (E := E) (e := e) he (q := fun _ ↦ p) hT
  simpa [finiteBernoulliHeteroEventProbability_const] using h

/-- The closed section of an increasing trace is increasing. -/
theorem IsIncreasingTrace.closedSection {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace (insert a E) T) :
    IsIncreasingTrace E T := by
  intro s t hst htE hs
  exact hT hst (by intro x hx; exact Finset.mem_insert.mpr (Or.inr (htE hx))) hs

/-- The open section of an increasing trace is increasing. -/
theorem IsIncreasingTrace.openSection {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} {T : Set (Finset ι)}
    (hT : IsIncreasingTrace (insert a E) T) :
    IsIncreasingTrace E {s : Finset ι | insert a s ∈ T} := by
  intro s t hst htE hs
  exact hT (Finset.insert_subset_insert a hst) (Finset.insert_subset_insert a htE) hs

/-- If a fresh coordinate `a` is already open, pivotality of another coordinate `e` is pivotality
inside the open section. -/
theorem isPivotalTrace_insert_fresh_iff_openSection {ι : Type*} [DecidableEq ι]
    (T : Set (Finset ι)) {a e : ι} (hae : a ≠ e) (s : Finset ι) :
    IsPivotalTrace T e (insert a s) ↔
      IsPivotalTrace {u : Finset ι | insert a u ∈ T} e s := by
  unfold IsPivotalTrace finiteForceOpen finiteForceClosed
  have hopen : insert e (insert a s) = insert a (insert e s) := by
    ext x
    simp [or_left_comm]
  have hclosed : (insert a s).erase e = insert a (s.erase e) := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [hae.symm]
    · simp [hxe]
  rw [hopen, hclosed]
  rfl

/-- The pivotal probability of the fresh coordinate is the difference between the open and closed
section probabilities. This is the finite-coordinate version of the first term in Russo's
formula. -/
theorem finiteBernoulliEventProbability_pivotal_fresh_eq_open_sub_closed {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ)
    {T : Set (Finset ι)} (hT : IsIncreasingTrace (insert a E) T) :
    finiteBernoulliEventProbability (insert a E) p
        {s : Finset ι | IsPivotalTrace T a s} =
      finiteBernoulliEventProbability E p {s : Finset ι | insert a s ∈ T} -
        finiteBernoulliEventProbability E p T := by
  let P : Set (Finset ι) := {s | IsPivotalTrace T a s}
  have hP : ∀ ⦃s : Finset ι⦄, s ⊆ E → (insert a s ∈ P ↔ s ∈ P) := by
    intro s _hsE
    exact isPivotalTrace_insert T a s
  rw [finiteBernoulliEventProbability_insert_invariant ha p P hP]
  unfold finiteBernoulliEventProbability
  unfold finiteBernoulliExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hsE : s ⊆ E := Finset.mem_powerset.mp hs
  have hdiff := indicator_insert_sub_eq_pivotalTrace ha hT hsE
  have hdiffP :
      T.indicator (fun _ ↦ (1 : ℝ)) (insert a s) -
          T.indicator (fun _ ↦ (1 : ℝ)) s =
        P.indicator (fun _ ↦ (1 : ℝ)) s := by
    simpa [P] using hdiff
  have hsec :
      ({u : Finset ι | insert a u ∈ T}).indicator (fun _ ↦ (1 : ℝ)) s =
        T.indicator (fun _ ↦ (1 : ℝ)) (insert a s) := by
    by_cases hsT : insert a s ∈ T <;> simp [hsT]
  simp only
  rw [hsec, ← hdiffP]
  ring

/-- Conditioning decomposition for pivotality of an old coordinate after inserting a fresh
coordinate. -/
theorem finiteBernoulliEventProbability_pivotal_old_insert_split {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {a e : ι} (ha : a ∉ E) (he : e ∈ E) (p : ℝ)
    (T : Set (Finset ι)) :
    finiteBernoulliEventProbability (insert a E) p
        {s : Finset ι | IsPivotalTrace T e s} =
      (1 - p) * finiteBernoulliEventProbability E p
          {s : Finset ι | IsPivotalTrace T e s} +
        p * finiteBernoulliEventProbability E p
          {s : Finset ι | IsPivotalTrace {u : Finset ι | insert a u ∈ T} e s} := by
  rw [finiteBernoulliEventProbability_insert_split ha]
  congr 2
  apply finiteBernoulliEventProbability_congr
  intro s _hsE
  have hae : a ≠ e := by
    intro h
    exact ha (by simpa [h] using he)
  exact isPivotalTrace_insert_fresh_iff_openSection T hae s

/-- Finite homogeneous Russo formula for increasing finite traces. For a finite increasing event,
the derivative of its Bernoulli probability is the sum of the probabilities that each coordinate
is pivotal. -/
theorem finiteBernoulliEventProbability_hasDerivAt {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} {T : Set (Finset ι)} (hT : IsIncreasingTrace E T) :
    HasDerivAt (fun x : ℝ ↦ finiteBernoulliEventProbability E x T)
      (E.sum fun e ↦ finiteBernoulliEventProbability E p
        {s : Finset ι | IsPivotalTrace T e s}) p := by
  induction E using Finset.induction generalizing T with
  | empty =>
      simpa [finiteBernoulliEventProbability, finiteBernoulliExpectation]
        using hasDerivAt_const p (T.indicator (fun _ ↦ (1 : ℝ)) (∅ : Finset ι))
  | insert a E ha ih =>
      let Topen : Set (Finset ι) := {s | insert a s ∈ T}
      have hclosed : IsIncreasingTrace E T := hT.closedSection
      have hopen : IsIncreasingTrace E Topen := hT.openSection
      have hclosed_deriv := ih hclosed
      have hopen_deriv := ih hopen
      have hsplit_fun :
          (fun x : ℝ ↦ finiteBernoulliEventProbability (insert a E) x T) =
            (fun x : ℝ ↦ (1 - x) * finiteBernoulliEventProbability E x T +
              x * finiteBernoulliEventProbability E x Topen) := by
        funext x
        simpa [Topen] using finiteBernoulliEventProbability_insert_split ha x T
      rw [hsplit_fun]
      have hone_sub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
        simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
      have hleft := hone_sub.mul hclosed_deriv
      have hright := (hasDerivAt_id p).mul hopen_deriv
      have hderiv := hleft.add hright
      apply hderiv.congr_deriv
      rw [Finset.sum_insert ha]
      have hfresh := finiteBernoulliEventProbability_pivotal_fresh_eq_open_sub_closed ha p hT
      have hold : ∀ e ∈ E,
          finiteBernoulliEventProbability (insert a E) p
              {s : Finset ι | IsPivotalTrace T e s} =
            (1 - p) * finiteBernoulliEventProbability E p
                {s : Finset ι | IsPivotalTrace T e s} +
              p * finiteBernoulliEventProbability E p
                {s : Finset ι | IsPivotalTrace Topen e s} := by
        intro e he
        simpa [Topen] using finiteBernoulliEventProbability_pivotal_old_insert_split ha he p T
      rw [hfresh]
      rw [show E.sum (fun e ↦ finiteBernoulliEventProbability (insert a E) p
              {s : Finset ι | IsPivotalTrace T e s}) =
            E.sum (fun e ↦
              (1 - p) * finiteBernoulliEventProbability E p
                  {s : Finset ι | IsPivotalTrace T e s} +
                p * finiteBernoulliEventProbability E p
                  {s : Finset ι | IsPivotalTrace Topen e s}) by
        apply Finset.sum_congr rfl
        intro e he
        exact hold e he]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      simp [Topen]
      ring

/-- Finite-support product-measure Russo formula. The derivative is the finite trace polynomial,
and the derivative value is written as the sum of actual product-measure pivotal probabilities. -/
theorem DependsOn.finiteSupport_setBernoulli_real_russo_hasDerivAt {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A)
    (hAinc : IsIncreasingEvent A) (p : I) :
    HasDerivAt
      (fun x : ℝ ↦ finiteBernoulliEventProbability E x (eventTrace E A))
      (E.sum fun e ↦ setBer((Set.univ : Set ι), p).real {ω : Set ι | IsPivotal A e ω})
      (p : ℝ) := by
  have hfinite := finiteBernoulliEventProbability_hasDerivAt
    (E := E) (p := (p : ℝ)) (T := eventTrace E A) hAinc.eventTrace
  apply hfinite.congr_deriv
  apply Finset.sum_congr rfl
  intro e he
  exact (hA.setBernoulli_real_pivotal_eq_finiteBernoulliEventProbability he p).symm

/-- Finite-support Russo formula for Bernoulli bond percolation events, with the derivative
written as a sum of actual `bernoulliBondMeasure` pivotal probabilities. -/
theorem DependsOn.bernoulliBondMeasure_real_russo_hasDerivAt (d : ℕ)
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)}
    (hA : DependsOn E A) (hAinc : IsIncreasingEvent A) (p : I) :
    HasDerivAt
      (fun x : ℝ ↦ finiteBernoulliEventProbability E x (eventTrace E A))
      (E.sum fun e ↦ (bernoulliBondMeasure d p).real
        {ω : EdgeConfiguration d | IsPivotal A e ω})
      (p : ℝ) := by
  simpa [bernoulliBondMeasure] using
    hA.finiteSupport_setBernoulli_real_russo_hasDerivAt hAinc p

/-- Finite difference of an observable when coordinate `e` is forced open instead of closed. This
is Grimmett's `δ_e X` on a finite cube. -/
def finiteDifference {ι : Type*} [DecidableEq ι]
    (e : ι) (X : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  X (finiteForceOpen e s) - X (finiteForceClosed e s)

/-- If a fresh coordinate `a` is already open, the finite difference in another coordinate passes
to the open section. -/
theorem finiteDifference_insert_fresh {ι : Type*} [DecidableEq ι]
    {a e : ι} (hae : a ≠ e) (X : Finset ι → ℝ) (s : Finset ι) :
    finiteDifference e X (insert a s) =
      finiteDifference e (fun u ↦ X (insert a u)) s := by
  unfold finiteDifference finiteForceOpen finiteForceClosed
  have hopen : insert e (insert a s) = insert a (insert e s) := by
    ext x
    simp [or_left_comm]
  have hclosed : (insert a s).erase e = insert a (s.erase e) := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [hae.symm]
    · simp [hxe]
  rw [hopen, hclosed]

/-- The expected finite difference in a fresh coordinate is the open-section expectation minus the
closed-section expectation. -/
theorem finiteBernoulliExpectation_finiteDifference_fresh {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {a : ι} (ha : a ∉ E) (p : ℝ) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p (finiteDifference a X) =
      finiteBernoulliExpectation E p (fun s ↦ X (insert a s)) -
        finiteBernoulliExpectation E p X := by
  rw [finiteBernoulliExpectation_insert_split ha]
  have hclosed : finiteBernoulliExpectation E p (finiteDifference a X) =
      finiteBernoulliExpectation E p (fun s ↦ X (insert a s) - X s) := by
    apply finiteBernoulliExpectation_congr
    intro s hsE
    have hnot : a ∉ s := Finset.notMem_mono hsE ha
    simp [finiteDifference, finiteForceOpen, finiteForceClosed, hnot]
  have hopen :
      finiteBernoulliExpectation E p (fun s ↦ finiteDifference a X (insert a s)) =
        finiteBernoulliExpectation E p (fun s ↦ X (insert a s) - X s) := by
    apply finiteBernoulliExpectation_congr
    intro s hsE
    have hnot : a ∉ s := Finset.notMem_mono hsE ha
    simp [finiteDifference, finiteForceOpen, finiteForceClosed, hnot]
  rw [hclosed, hopen]
  rw [finiteBernoulliExpectation_sub]
  ring

/-- Conditioning decomposition for finite differences in an old coordinate after inserting a fresh
coordinate. -/
theorem finiteBernoulliExpectation_finiteDifference_old_insert_split {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {a e : ι} (ha : a ∉ E) (he : e ∈ E) (p : ℝ)
    (X : Finset ι → ℝ) :
    finiteBernoulliExpectation (insert a E) p (finiteDifference e X) =
      (1 - p) * finiteBernoulliExpectation E p (finiteDifference e X) +
        p * finiteBernoulliExpectation E p
          (finiteDifference e (fun s ↦ X (insert a s))) := by
  rw [finiteBernoulliExpectation_insert_split ha]
  congr 2
  apply finiteBernoulliExpectation_congr
  intro s _hsE
  have hae : a ≠ e := by
    intro h
    exact ha (by simpa [h] using he)
  exact finiteDifference_insert_fresh hae X s

/-- Finite Russo formula for real-valued observables on a finite Bernoulli cube. The derivative of
`E_p[X]` is the sum of the expectations of the finite differences `δ_e X`. This is the finite
random-variable form behind Grimmett's later Russo formulas. -/
theorem finiteBernoulliExpectation_hasDerivAt {ι : Type*} [DecidableEq ι]
    {E : Finset ι} {p : ℝ} (X : Finset ι → ℝ) :
    HasDerivAt (fun x : ℝ ↦ finiteBernoulliExpectation E x X)
      (E.sum fun e ↦ finiteBernoulliExpectation E p (finiteDifference e X)) p := by
  induction E using Finset.induction generalizing X with
  | empty =>
      simpa [finiteBernoulliExpectation]
        using hasDerivAt_const p (X (∅ : Finset ι))
  | insert a E ha ih =>
      let Xopen : Finset ι → ℝ := fun s ↦ X (insert a s)
      have hclosed_deriv := ih X
      have hopen_deriv := ih Xopen
      have hsplit_fun :
          (fun x : ℝ ↦ finiteBernoulliExpectation (insert a E) x X) =
            (fun x : ℝ ↦ (1 - x) * finiteBernoulliExpectation E x X +
              x * finiteBernoulliExpectation E x Xopen) := by
        funext x
        simpa [Xopen] using finiteBernoulliExpectation_insert_split ha x X
      rw [hsplit_fun]
      have hone_sub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) p := by
        simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
      have hleft := hone_sub.mul hclosed_deriv
      have hright := (hasDerivAt_id p).mul hopen_deriv
      have hderiv := hleft.add hright
      apply hderiv.congr_deriv
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
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      simp [Xopen]
      ring

/-- Iterated finite difference `δ_f δ_e X`. -/
def finiteSecondDifference {ι : Type*} [DecidableEq ι]
    (e f : ι) (X : Finset ι → ℝ) : Finset ι → ℝ :=
  finiteDifference f (finiteDifference e X)

/-- Finite second-derivative Russo formula for real-valued observables, stated as the derivative
of the first-difference sum. This is the finite double-sum precursor to Grimmett's second
derivative identities. -/
theorem finiteBernoulliExpectation_derivativeSum_hasDerivAt {ι : Type*}
    [DecidableEq ι] {E : Finset ι} {p : ℝ} (X : Finset ι → ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ E.sum fun e ↦ finiteBernoulliExpectation E x (finiteDifference e X))
      (E.sum fun e ↦ E.sum fun f ↦
        finiteBernoulliExpectation E p (finiteSecondDifference e f X)) p := by
  simpa [finiteSecondDifference] using
    HasDerivAt.fun_sum (u := E)
      (A := fun e x ↦ finiteBernoulliExpectation E x (finiteDifference e X))
      (A' := fun e ↦ E.sum fun f ↦
        finiteBernoulliExpectation E p (finiteDifference f (finiteDifference e X)))
      (x := p) (fun e _he ↦ finiteBernoulliExpectation_hasDerivAt (E := E)
        (p := p) (finiteDifference e X))

end Percolation
