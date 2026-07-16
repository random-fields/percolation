import Percolation.Critical.DynamicRevealCells

/-!
# Finite interval histories for dynamic renormalization

Equations (7.27), (7.31), and (7.32) record two kinds of information about a uniform label:
an edge is `beta(e)`-closed and/or `gamma(e)`-open.  Earlier restart boxes may overlap the
current one, so a source-faithful proof cannot simply call all earlier coordinates fresh.  The
finite profile below records the two supports separately and proves the exact algebraic step
needed by the construction: current closed-boundary information can be peeled from the history,
leaving a residual finite cylinder to which coordinate independence may be applied.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Finite common-uniform information of the form “closed at `lower`” and “open at `upper`”.
An edge may occur in either or both supports. -/
structure FiniteRevealIntervalProfile (ι : Type*) where
  closedSupport : Finset ι
  openSupport : Finset ι
  lower : ι → I
  upper : ι → I

namespace FiniteRevealIntervalProfile

variable {ι : Type*} [DecidableEq ι]

/-- All coordinates on which the interval history depends. -/
def support (P : FiniteRevealIntervalProfile ι) : Finset ι :=
  P.closedSupport ∪ P.openSupport

/-- Literal label-space interval history.  Closed information uses `lower ≤ X`; open
information uses the same strict convention `X < upper` as `thresholdConfiguration`. -/
def event (P : FiniteRevealIntervalProfile ι) : Set (ι → ℝ) :=
  {X | (∀ e ∈ P.closedSupport, (P.lower e : ℝ) ≤ X e) ∧
    ∀ e ∈ P.openSupport, X e < (P.upper e : ℝ)}

omit [DecidableEq ι] in
@[simp]
theorem mem_event_iff (P : FiniteRevealIntervalProfile ι) (X : ι → ℝ) :
    X ∈ P.event ↔
      (∀ e ∈ P.closedSupport, (P.lower e : ℝ) ≤ X e) ∧
        ∀ e ∈ P.openSupport, X e < (P.upper e : ℝ) :=
  Iff.rfl

/-- The interval history is a cylinder on exactly the union of its two finite supports. -/
theorem measurableSet_event_coordSigma (P : FiniteRevealIntervalProfile ι) :
    MeasurableSet[coordSigma ι (P.support : Set ι)] P.event := by
  have hrepr : P.event =
      (⋂ e ∈ (P.closedSupport : Set ι),
          (fun X : ι → ℝ ↦ X e) ⁻¹' Set.Ici (P.lower e : ℝ)) ∩
        ⋂ e ∈ (P.openSupport : Set ι),
          (fun X : ι → ℝ ↦ X e) ⁻¹' Set.Iio (P.upper e : ℝ) := by
    ext X
    simp [event]
  rw [hrepr]
  apply MeasurableSet.inter
  · apply MeasurableSet.biInter P.closedSupport.countable_toSet
    intro e he
    exact measurable_eval_coordSigma (Finset.mem_union_left _ he) measurableSet_Ici
  · apply MeasurableSet.biInter P.openSupport.countable_toSet
    intro e he
    exact measurable_eval_coordSigma (Finset.mem_union_right _ he) measurableSet_Iio

theorem measurableSet_event (P : FiniteRevealIntervalProfile ι) :
    MeasurableSet P.event :=
  (coordSigma_le _) _ P.measurableSet_event_coordSigma

/-- Remove the closed constraints that will be represented by the current boundary history.
Open constraints are deliberately retained: the later geometric invariant must prove that no
such constraint lies on the current restart support. -/
def withoutClosed (P : FiniteRevealIntervalProfile ι) (E : Finset ι) :
    FiniteRevealIntervalProfile ι where
  closedSupport := P.closedSupport \ E
  openSupport := P.openSupport
  lower := P.lower
  upper := P.upper

@[simp]
theorem withoutClosed_closedSupport (P : FiniteRevealIntervalProfile ι) (E : Finset ι) :
    (P.withoutClosed E).closedSupport = P.closedSupport \ E :=
  rfl

@[simp]
theorem withoutClosed_openSupport (P : FiniteRevealIntervalProfile ι) (E : Finset ι) :
    (P.withoutClosed E).openSupport = P.openSupport :=
  rfl

/-- Exact interval-fiber identity: if every current boundary coordinate already carries its
`lower`-closed constraint, the old history is the residual cylinder intersected with the
current `boundaryClosedHistoryEvent`. -/
theorem event_eq_withoutClosed_inter_boundaryClosedHistoryEvent
    (P : FiniteRevealIntervalProfile ι) (E : Finset ι)
    (hE : E ⊆ P.closedSupport) :
    P.event = (P.withoutClosed E).event ∩
      boundaryClosedHistoryEvent E P.lower := by
  ext X
  constructor
  · intro hX
    refine ⟨⟨?_, hX.2⟩, ?_⟩
    · intro e he
      exact hX.1 e (Finset.mem_sdiff.mp he).1
    · intro e he
      exact hX.1 e (hE he)
  · rintro ⟨hResidual, hBoundary⟩
    refine ⟨?_, hResidual.2⟩
    intro e heClosed
    by_cases heE : e ∈ E
    · exact hBoundary e heE
    · exact hResidual.1 e (Finset.mem_sdiff.mpr ⟨heClosed, heE⟩)

/-- Support-level form of the residual freshness obligation. -/
theorem disjoint_withoutClosed_support
    (P : FiniteRevealIntervalProfile ι) (E Q : Finset ι)
    (hclosed : Disjoint ((P.closedSupport \ E : Finset ι) : Set ι) (Q : Set ι))
    (hopen : Disjoint (P.openSupport : Set ι) (Q : Set ι)) :
    Disjoint ((P.withoutClosed E).support : Set ι) (Q : Set ι) := by
  rw [Set.disjoint_left]
  intro e heSupport heQ
  change e ∈ (P.closedSupport \ E) ∪ P.openSupport at heSupport
  rw [Finset.mem_union] at heSupport
  rcases heSupport with heClosed | heOpen
  · exact Set.disjoint_left.mp hclosed heClosed heQ
  · exact Set.disjoint_left.mp hopen heOpen heQ

/-- Once the residual support is disjoint from a finite boundary, the interval event factors
from the heterogeneous closed-boundary event under the common-uniform product measure. -/
theorem couplingMeasure_real_event_inter_boundaryClosedHistoryEvent
    (P : FiniteRevealIntervalProfile ι) (E : Finset ι)
    (hdisjoint : Disjoint (P.support : Set ι) (E : Set ι))
    (beta : ι → I) :
    (couplingMeasure ι).real (P.event ∩ boundaryClosedHistoryEvent E beta) =
      (couplingMeasure ι).real P.event *
        (couplingMeasure ι).real (boundaryClosedHistoryEvent E beta) := by
  have hP := P.measurableSet_event_coordSigma
  have hH := measurableSet_boundaryClosedHistoryEvent_coordSigma E beta
  have hindep : IndepSet P.event (boundaryClosedHistoryEvent E beta)
      (couplingMeasure ι) :=
    indepSet_of_measurableSet_coordSigma_of_disjoint hdisjoint hP hH
  have hmass := congrArg ENNReal.toReal hindep.measure_inter_eq_mul
  simpa [Measure.real, ENNReal.toReal_mul] using hmass

/-! ### Finite threshold-pattern refinements -/

/-- Coordinates of a finite support whose labels lie strictly below `q`.  This generic
label-space version is deliberately separate from the cubic-edge-specific
`finiteEdgesBelow`: it can refine any interval history without importing the edge
exploration layer. -/
noncomputable def labelsBelow (E : Finset ι) (q : I) (X : ι → ℝ) : Finset ι := by
  classical
  exact E.filter fun e ↦ X e < (q : ℝ)

omit [DecidableEq ι] in
@[simp]
theorem mem_labelsBelow_iff {E : Finset ι} {q : I} {X : ι → ℝ} {e : ι} :
    e ∈ labelsBelow E q X ↔ e ∈ E ∧ X e < (q : ℝ) := by
  classical
  simp [labelsBelow]

/-- Refine an interval history by the exact `< q` pattern `A` on the finite support `E`.
The definition normalizes junk values of `A` by intersecting them with `E`.  On a coordinate
already constrained by `P`, the new lower bound is joined with `q` and the new upper bound is
met with `q`; on a fresh coordinate it is exactly `q`. -/
noncomputable def refineAtThreshold (P : FiniteRevealIntervalProfile ι)
    (E : Finset ι) (q : I) (A : Finset ι) : FiniteRevealIntervalProfile ι := by
  classical
  let A' := E ∩ A
  exact
    { closedSupport := P.closedSupport ∪ (E \ A')
      openSupport := P.openSupport ∪ A'
      lower := fun e ↦
        if e ∈ E \ A' then
          if e ∈ P.closedSupport then max (P.lower e) q else q
        else P.lower e
      upper := fun e ↦
        if e ∈ A' then
          if e ∈ P.openSupport then min (P.upper e) q else q
        else P.upper e }

@[simp]
theorem coe_max_unitInterval (a b : I) :
    ((max a b : I) : ℝ) = max (a : ℝ) (b : ℝ) :=
  rfl

@[simp]
theorem coe_min_unitInterval (a b : I) :
    ((min a b : I) : ℝ) = min (a : ℝ) (b : ℝ) :=
  rfl

/-- Exact semantics of `refineAtThreshold`: its event is the old interval cell intersected
with one complete finite threshold-pattern fiber. -/
theorem refineAtThreshold_event_eq (P : FiniteRevealIntervalProfile ι)
    (E : Finset ι) (q : I) (A : Finset ι) :
    (P.refineAtThreshold E q A).event =
      P.event ∩ {X | labelsBelow E q X = E ∩ A} := by
  classical
  ext X
  simp only [event, refineAtThreshold, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hclosed, hopen⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro e heP
      have h := hclosed e (Finset.mem_union_left _ heP)
      by_cases heNew : e ∈ E \ (E ∩ A)
      · have heE : e ∈ E := (Finset.mem_sdiff.mp heNew).1
        have heNotA : e ∉ A := by
          intro heA
          exact (Finset.mem_sdiff.mp heNew).2 (Finset.mem_inter.mpr ⟨heE, heA⟩)
        simp only [if_pos heNew, if_pos heP] at h
        change ((max (P.lower e) q : I) : ℝ) ≤ X e at h
        rw [coe_max_unitInterval, max_le_iff] at h
        exact h.1
      · have heNewLogic : ¬ (e ∈ E ∧ e ∉ A) := by
          rintro ⟨heE, heNotA⟩
          exact heNew (Finset.mem_sdiff.mpr
            ⟨heE, fun heEA ↦ heNotA (Finset.mem_inter.mp heEA).2⟩)
        simpa [heNewLogic] using h
    · intro e heP
      have h := hopen e (Finset.mem_union_left _ heP)
      by_cases heNew : e ∈ E ∩ A
      · simp [heNew, heP] at h
        exact h.1
      · simpa [heNew] using h
    · ext e
      simp only [mem_labelsBelow_iff, Finset.mem_inter]
      constructor
      · rintro ⟨heE, heOpen⟩
        refine ⟨heE, ?_⟩
        by_contra heNotA
        have heClosed : e ∈ E \ (E ∩ A) := by
          simp [heE, heNotA]
        have h := hclosed e (Finset.mem_union_right _ heClosed)
        by_cases heP : e ∈ P.closedSupport
        · simp only [if_pos heClosed, if_pos heP] at h
          change ((max (P.lower e) q : I) : ℝ) ≤ X e at h
          rw [coe_max_unitInterval, max_le_iff] at h
          have hq : (q : ℝ) ≤ X e := h.2
          exact (not_lt_of_ge hq) heOpen
        · have hq : (q : ℝ) ≤ X e := by
            simp only [if_pos heClosed, if_neg heP] at h
            change (q : ℝ) ≤ X e at h
            exact h
          exact (not_lt_of_ge hq) heOpen
      · rintro ⟨heE, heA⟩
        refine ⟨heE, ?_⟩
        have heOpenPattern : e ∈ E ∩ A := Finset.mem_inter.mpr ⟨heE, heA⟩
        have h := hopen e (Finset.mem_union_right _ heOpenPattern)
        by_cases heP : e ∈ P.openSupport
        · simp [heOpenPattern, heP] at h
          exact h.2
        · simpa [heOpenPattern, heP] using h
  · rintro ⟨hP, hpattern⟩
    have hpatternIff : ∀ e ∈ E, (X e < (q : ℝ) ↔ e ∈ A) := by
      intro e heE
      have heq := Finset.ext_iff.mp hpattern e
      simpa [mem_labelsBelow_iff, heE] using heq
    refine ⟨?_, ?_⟩
    · intro e heUnion
      rw [Finset.mem_union] at heUnion
      rcases heUnion with heP | heClosed
      · by_cases heNew : e ∈ E \ (E ∩ A)
        · have heE : e ∈ E := (Finset.mem_sdiff.mp heNew).1
          have heNotA : e ∉ A := by
            intro heA
            exact (Finset.mem_sdiff.mp heNew).2 (Finset.mem_inter.mpr ⟨heE, heA⟩)
          have hq : (q : ℝ) ≤ X e :=
            le_of_not_gt fun hlt ↦ heNotA ((hpatternIff e heE).mp hlt)
          have hOld := hP.1 e heP
          simp only [if_pos heNew, if_pos heP]
          change ((max (P.lower e) q : I) : ℝ) ≤ X e
          rw [coe_max_unitInterval, max_le_iff]
          exact ⟨hOld, hq⟩
        · have heNewLogic : ¬ (e ∈ E ∧ e ∉ A) := by
            rintro ⟨heE, heNotA⟩
            exact heNew (Finset.mem_sdiff.mpr
              ⟨heE, fun heEA ↦ heNotA (Finset.mem_inter.mp heEA).2⟩)
          simpa [heNewLogic] using hP.1 e heP
      · have heE : e ∈ E := (Finset.mem_sdiff.mp heClosed).1
        have heNotA : e ∉ A := by
          intro heA
          exact (Finset.mem_sdiff.mp heClosed).2 (Finset.mem_inter.mpr ⟨heE, heA⟩)
        have hq : (q : ℝ) ≤ X e :=
          le_of_not_gt fun hlt ↦ heNotA ((hpatternIff e heE).mp hlt)
        by_cases heP : e ∈ P.closedSupport
        · have hOld := hP.1 e heP
          simp only [if_pos heClosed, if_pos heP]
          change ((max (P.lower e) q : I) : ℝ) ≤ X e
          rw [coe_max_unitInterval, max_le_iff]
          exact ⟨hOld, hq⟩
        · simp only [if_pos heClosed, if_neg heP]
          change (q : ℝ) ≤ X e
          exact hq
    · intro e heUnion
      rw [Finset.mem_union] at heUnion
      rcases heUnion with heP | heOpenPattern
      · by_cases heNew : e ∈ E ∩ A
        · have heE : e ∈ E := (Finset.mem_inter.mp heNew).1
          have heA : e ∈ A := (Finset.mem_inter.mp heNew).2
          have hq : X e < (q : ℝ) := (hpatternIff e heE).mpr heA
          have hOld := hP.2 e heP
          simp [heNew, heP, hOld, hq]
        · simpa [heNew] using hP.2 e heP
      · have heE : e ∈ E := (Finset.mem_inter.mp heOpenPattern).1
        have heA : e ∈ A := (Finset.mem_inter.mp heOpenPattern).2
        have hq : X e < (q : ℝ) := (hpatternIff e heE).mpr heA
        by_cases heP : e ∈ P.openSupport
        · have hOld := hP.2 e heP
          simp [heOpenPattern, heP, hOld, hq]
        · simpa [heOpenPattern, heP] using hq

omit [DecidableEq ι] in
/-- The threshold pattern of a realization is always a normalized subset of its support. -/
theorem labelsBelow_subset (E : Finset ι) (q : I) (X : ι → ℝ) :
    labelsBelow E q X ⊆ E := by
  intro e he
  exact (mem_labelsBelow_iff.mp he).1

/-- Equality of finite threshold patterns is exactly pointwise agreement of the corresponding
strict threshold tests on the advertised support. -/
theorem labelsBelow_eq_iff (E : Finset ι) (q : I) (X Y : ι → ℝ) :
    labelsBelow E q X = labelsBelow E q Y ↔
      ∀ e ∈ E, (X e < (q : ℝ) ↔ Y e < (q : ℝ)) := by
  constructor
  · intro h e heE
    have heq := Finset.ext_iff.mp h e
    simpa [mem_labelsBelow_iff, heE] using heq
  · intro h
    ext e
    by_cases heE : e ∈ E
    · simpa [mem_labelsBelow_iff, heE] using h e heE
    · simp [mem_labelsBelow_iff, heE]

/-- Refining by the pattern actually realized by `X` preserves membership. -/
theorem mem_refineAtThreshold_realized (P : FiniteRevealIntervalProfile ι)
    (E : Finset ι) (q : I) {X : ι → ℝ} (hX : X ∈ P.event) :
    X ∈ (P.refineAtThreshold E q (labelsBelow E q X)).event := by
  rw [refineAtThreshold_event_eq]
  refine ⟨hX, ?_⟩
  exact (Finset.inter_eq_right.mpr (labelsBelow_subset E q X)).symm

/-- Exact threshold refinements with distinct normalized patterns are disjoint. -/
theorem disjoint_refineAtThreshold_of_ne (P : FiniteRevealIntervalProfile ι)
    (E : Finset ι) (q : I) {A B : Finset ι}
    (hA : A ⊆ E) (hB : B ⊆ E) (hne : A ≠ B) :
    Disjoint (P.refineAtThreshold E q A).event
      (P.refineAtThreshold E q B).event := by
  rw [Set.disjoint_left]
  intro X hXA hXB
  rw [refineAtThreshold_event_eq] at hXA hXB
  have hEA : E ∩ A = A := Finset.inter_eq_right.mpr hA
  have hEB : E ∩ B = B := Finset.inter_eq_right.mpr hB
  exact hne (hEA ▸ hEB ▸ hXA.2.symm.trans hXB.2)

end FiniteRevealIntervalProfile

/-! ### Canonical classifier for a finite interval-profile partition -/

/-- Choose the unique interval profile containing a realization when one exists.  The default
is used only outside the covered history. -/
noncomputable def realizedIntervalProfileCell
    {ι C : Type*} [Fintype C] (default : C)
    (profile : C → FiniteRevealIntervalProfile ι) (X : ι → ℝ) : C := by
  classical
  exact if h : ∃ c, X ∈ (profile c).event then Classical.choose h else default

theorem realizedIntervalProfileCell_mem
    {ι C : Type*} [Fintype C] (default : C)
    (profile : C → FiniteRevealIntervalProfile ι) (X : ι → ℝ)
    (h : ∃ c, X ∈ (profile c).event) :
    X ∈ (profile (realizedIntervalProfileCell default profile X)).event := by
  classical
  simp only [realizedIntervalProfileCell, dif_pos h]
  exact Classical.choose_spec h

theorem realizedIntervalProfileCell_eq_of_mem
    {ι C : Type*} [Fintype C] (default : C)
    (profile : C → FiniteRevealIntervalProfile ι)
    (hpairwise : ∀ c c', c ≠ c' → Disjoint (profile c).event (profile c').event)
    {X : ι → ℝ} {c : C} (hc : X ∈ (profile c).event) :
    realizedIntervalProfileCell default profile X = c := by
  classical
  have hex : ∃ c', X ∈ (profile c').event := ⟨c, hc⟩
  have hchosen := realizedIntervalProfileCell_mem default profile X hex
  by_contra hne
  exact Set.disjoint_left.mp
    (hpairwise (realizedIntervalProfileCell default profile X) c hne)
      hchosen hc

/-- A finite pairwise-disjoint family of interval profiles that covers `history` is
automatically an exact `exactRevealCellEvent` realization.  This removes an otherwise
repetitive fiber proof from each dynamic-block stage. -/
theorem intervalProfile_event_eq_exactRevealCellEvent
    {ι C : Type*} [Fintype C] (default : C)
    (profile : C → FiniteRevealIntervalProfile ι) (history : Set (ι → ℝ))
    (hsub : ∀ c, (profile c).event ⊆ history)
    (hcover : history ⊆ ⋃ c, (profile c).event)
    (hpairwise : ∀ c c', c ≠ c' → Disjoint (profile c).event (profile c').event)
    (c : C) :
    (profile c).event =
      exactRevealCellEvent history (realizedIntervalProfileCell default profile) c := by
  classical
  ext X
  constructor
  · intro hX
    exact ⟨hsub c hX,
      realizedIntervalProfileCell_eq_of_mem default profile hpairwise hX⟩
  · rintro ⟨hXHistory, hcell⟩
    have hcovered := hcover hXHistory
    rw [Set.mem_iUnion] at hcovered
    have hmem := realizedIntervalProfileCell_mem default profile X hcovered
    rw [hcell] at hmem
    exact hmem

end Percolation
