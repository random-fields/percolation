import Percolation.Bernoulli.UpwardDistance
import Percolation.Critical.SeedAmplification

/-!
# Boundary restart and sprinkling for Grimmett Lemma 7.17

This file separates the finite-coordinate probability kernel from the later geometric
construction of the available exit set `U(K)`.  Histories are stated without division, so null
histories remain meaningful; the conditional-ratio theorem is derived only after positivity.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval BigOperators

/-- The history `H`: every boundary coordinate is closed at its individual threshold. -/
def boundaryClosedHistoryEvent {iota : Type*} (E : Finset iota) (beta : iota → I) :
    Set (iota → ℝ) :=
  {X | ∀ e ∈ E, (beta e : ℝ) ≤ X e}

/-- At least one currently available exit edge opens in its threshold increment of width
`delta`.  The finite set `U X` is required later to depend only on coordinates off `E`. -/
def sprinkledAvailableExitEvent {iota : Type*} (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota) : Set (iota → ℝ) :=
  {X | ∃ e ∈ U X, X e < (beta e : ℝ) + delta}

/-- The complementary event that none of the currently available exits opens during the
threshold increment.  Keeping this event explicit makes the exact finite-coordinate
factorization used in Lemma 7.17 available without any division by a history probability. -/
def sprinkledAvailableExitFailureEvent {iota : Type*} (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota) : Set (iota → ℝ) :=
  {X | ∀ e ∈ U X, (beta e : ℝ) + delta ≤ X e}

/-- The off-boundary cell on which the set of available exits is exactly `S`. -/
def exactAvailableExitSetEvent {iota : Type*}
    (U : (iota → ℝ) → Finset iota) (S : Finset iota) : Set (iota → ℝ) :=
  {X | U X = S}

/-- The available-exit set has cardinality at most `t`. -/
def fewAvailableExitsEvent {iota : Type*}
    (U : (iota → ℝ) → Finset iota) (t : ℕ) : Set (iota → ℝ) :=
  {X | (U X).card ≤ t}

/-- Candidate exit sets larger than `t`, all drawn from the boundary support `E`. -/
def largeAvailableExitSets {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (t : ℕ) : Finset (Finset iota) :=
  E.powerset.filter fun S => t < S.card

theorem sprinkledAvailableExitFailureEvent_eq_compl {iota : Type*}
    (beta : iota → I) (delta : ℝ) (U : (iota → ℝ) → Finset iota) :
    sprinkledAvailableExitFailureEvent beta delta U =
      (sprinkledAvailableExitEvent beta delta U)ᶜ := by
  ext X
  simp [sprinkledAvailableExitFailureEvent, sprinkledAvailableExitEvent]

theorem pairwiseDisjoint_exactAvailableExitSetEvent {iota : Type*}
    (U : (iota → ℝ) → Finset iota) (C : Finset (Finset iota)) :
    Set.PairwiseDisjoint (C : Set (Finset iota)) (exactAvailableExitSetEvent U) := by
  intro S hS T hT hST
  rw [Set.disjoint_left]
  intro X hXS hXT
  exact hST ((show U X = S from hXS).symm.trans hXT)

theorem measurableSet_fewAvailableExitsEvent_coordSigma {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (U : (iota → ℝ) → Finset iota) (t : ℕ)
    (hU : ∀ X, U X ⊆ E)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)] (fewAvailableExitsEvent U t) := by
  have hevent : fewAvailableExitsEvent U t =
      ⋃ S ∈ E.powerset.filter (fun S => S.card ≤ t), exactAvailableExitSetEvent U S := by
    ext X
    simp only [fewAvailableExitsEvent, Set.mem_setOf_eq, Set.mem_iUnion,
      Finset.mem_filter, Finset.mem_powerset, exactAvailableExitSetEvent]
    constructor
    · intro hcard
      exact ⟨U X, ⟨hU X, hcard⟩, rfl⟩
    · rintro ⟨S, ⟨hSE, hcard⟩, hUS⟩
      simpa [hUS] using hcard
  rw [hevent]
  exact MeasurableSet.biUnion_finset fun S hS => hexact S (Finset.mem_powerset.mp
    (Finset.mem_of_mem_filter hS))

theorem measurableSet_boundaryClosedHistoryEvent {iota : Type*}
    (E : Finset iota) (beta : iota → I) :
    MeasurableSet (boundaryClosedHistoryEvent E beta) := by
  have hrepr : boundaryClosedHistoryEvent E beta =
      (E : Set iota).pi fun e => Set.Ici (beta e : ℝ) := by
    ext X
    simp [boundaryClosedHistoryEvent, Set.mem_pi]
  rw [hrepr]
  exact MeasurableSet.pi E.countable_toSet fun e _he => measurableSet_Ici

theorem measurableSet_boundaryClosedHistoryEvent_coordSigma {iota : Type*}
    (E : Finset iota) (beta : iota → I) :
    MeasurableSet[coordSigma iota (E : Set iota)]
      (boundaryClosedHistoryEvent E beta) := by
  have hrepr : boundaryClosedHistoryEvent E beta =
      ⋂ e ∈ (E : Set iota), (fun X : iota → ℝ => X e) ⁻¹' Set.Ici (beta e : ℝ) := by
    ext X
    simp [boundaryClosedHistoryEvent]
  rw [hrepr]
  exact MeasurableSet.biInter E.countable_toSet fun e he =>
    measurable_eval_coordSigma he measurableSet_Ici

/-- Exact mass of the heterogeneous closed-boundary history. -/
theorem couplingMeasure_boundaryClosedHistoryEvent
    {iota : Type*} (E : Finset iota) (beta : iota → I) :
    couplingMeasure iota (boundaryClosedHistoryEvent E beta) =
      ∏ e ∈ E, ENNReal.ofReal (1 - (beta e : ℝ)) := by
  have hrepr : boundaryClosedHistoryEvent E beta =
      (E : Set iota).pi fun e => Set.Ici (beta e : ℝ) := by
    ext X
    simp [boundaryClosedHistoryEvent, Set.mem_pi]
  rw [hrepr]
  have hfactor := couplingMeasure_pi_inter E
    (S := fun e => Set.Ici (beta e : ℝ)) (fun _e => measurableSet_Ici)
    (C := Set.univ) (MeasurableSet.univ :
      MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)] Set.univ)
  simp only [Set.inter_univ, measure_univ, mul_one] at hfactor
  rw [hfactor]
  apply Finset.prod_congr rfl
  intro e _he
  exact volume_restrict_Icc_Ici (beta e)

theorem couplingMeasure_real_boundaryClosedHistoryEvent
    {iota : Type*} (E : Finset iota) (beta : iota → I) :
    (couplingMeasure iota).real (boundaryClosedHistoryEvent E beta) =
      ∏ e ∈ E, (1 - (beta e : ℝ)) := by
  rw [Measure.real, couplingMeasure_boundaryClosedHistoryEvent, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _he
  rw [ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (beta e).2.2

theorem couplingMeasure_real_boundaryClosedHistoryEvent_pos
    {iota : Type*} (E : Finset iota) (beta : iota → I)
    (hbeta : ∀ e ∈ E, (beta e : ℝ) < 1) :
    0 < (couplingMeasure iota).real (boundaryClosedHistoryEvent E beta) := by
  rw [couplingMeasure_real_boundaryClosedHistoryEvent]
  exact Finset.prod_pos fun e he => sub_pos.mpr (hbeta e he)

/-- Raise precisely the thresholds indexed by `S` by `delta`. -/
def incrementedBoundaryThreshold {iota : Type*} [DecidableEq iota]
    (beta : iota → I) (delta : ℝ) (S : Finset iota)
    (hdelta : 0 ≤ delta) (hupper : ∀ e ∈ S, (beta e : ℝ) + delta ≤ 1) :
    iota → I := fun e =>
  if he : e ∈ S then
    ⟨(beta e : ℝ) + delta, add_nonneg (beta e).2.1 hdelta, hupper e he⟩
  else beta e

@[simp]
theorem coe_incrementedBoundaryThreshold_of_mem {iota : Type*} [DecidableEq iota]
    (beta : iota → I) (delta : ℝ) (S : Finset iota)
    (hdelta : 0 ≤ delta) (hupper : ∀ e ∈ S, (beta e : ℝ) + delta ≤ 1)
    {e : iota} (he : e ∈ S) :
    (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ) =
      (beta e : ℝ) + delta := by
  simp [incrementedBoundaryThreshold, he]

@[simp]
theorem coe_incrementedBoundaryThreshold_of_notMem {iota : Type*} [DecidableEq iota]
    (beta : iota → I) (delta : ℝ) (S : Finset iota)
    (hdelta : 0 ≤ delta) (hupper : ∀ e ∈ S, (beta e : ℝ) + delta ≤ 1)
    {e : iota} (he : e ∉ S) :
    (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ) =
      (beta e : ℝ) := by
  simp [incrementedBoundaryThreshold, he]

/-- The elementary product comparison behind the conditional sprinkling estimate. -/
theorem prod_one_sub_incrementedBoundaryThreshold_le
    {iota : Type*} [DecidableEq iota]
    (E S : Finset iota) (hSE : S ⊆ E) (beta : iota → I) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hupper : ∀ e ∈ S, (beta e : ℝ) + delta ≤ 1) :
    (∏ e ∈ E,
        (1 - (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ))) ≤
      (1 - delta) ^ S.card * ∏ e ∈ E, (1 - (beta e : ℝ)) := by
  have hterm : ∀ e ∈ E,
      1 - (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ) ≤
        (if e ∈ S then 1 - delta else 1) * (1 - (beta e : ℝ)) := by
    intro e heE
    by_cases heS : e ∈ S
    · rw [coe_incrementedBoundaryThreshold_of_mem beta delta S hdelta hupper heS,
        if_pos heS]
      nlinarith [(beta e).2.1]
    · rw [coe_incrementedBoundaryThreshold_of_notMem beta delta S hdelta hupper heS,
        if_neg heS, one_mul]
  calc
    (∏ e ∈ E,
        (1 - (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ))) ≤
      ∏ e ∈ E, ((if e ∈ S then 1 - delta else 1) *
        (1 - (beta e : ℝ))) := by
      exact Finset.prod_le_prod (fun e _he => by
        exact sub_nonneg.mpr (incrementedBoundaryThreshold beta delta S hdelta hupper e).2.2)
        hterm
    _ = (∏ e ∈ E, (if e ∈ S then 1 - delta else 1)) *
        ∏ e ∈ E, (1 - (beta e : ℝ)) := by
      rw [Finset.prod_mul_distrib]
    _ = (1 - delta) ^ S.card * ∏ e ∈ E, (1 - (beta e : ℝ)) := by
      congr 1
      calc
        (∏ e ∈ E, (if e ∈ S then 1 - delta else 1)) =
            ∏ e ∈ S, (if e ∈ S then 1 - delta else 1) := by
          symm
          apply Finset.prod_subset hSE
          intro e _heE heS
          simp [heS]
        _ = ∏ _e ∈ S, (1 - delta) := by simp
        _ = (1 - delta) ^ S.card := by simp

/-- On a cell where the available exit set is the fixed finite set `S`, the history-and-failure
event is exactly a heterogeneous closed-coordinate box with thresholds incremented on `S`.
This is the finite probability identity at the heart of Grimmett's Lemma 7.17. -/
theorem couplingMeasure_sprinkledFailure_inter_history_inter_exact
    {iota : Type*} [DecidableEq iota]
    (E S : Finset iota) (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota)
    (hSE : S ⊆ E) (hdelta : 0 ≤ delta)
    (hupper : ∀ e ∈ S, (beta e : ℝ) + delta ≤ 1)
    (hexact : MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    couplingMeasure iota
        (sprinkledAvailableExitFailureEvent beta delta U ∩
          boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S) =
      (∏ e ∈ E, ENNReal.ofReal
          (1 - (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ))) *
        couplingMeasure iota (exactAvailableExitSetEvent U S) := by
  let beta' := incrementedBoundaryThreshold beta delta S hdelta hupper
  have hevent :
      sprinkledAvailableExitFailureEvent beta delta U ∩
          boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S =
        (E : Set iota).pi (fun e => Set.Ici (beta' e : ℝ)) ∩
          exactAvailableExitSetEvent U S := by
    ext X
    simp only [Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe,
      sprinkledAvailableExitFailureEvent, boundaryClosedHistoryEvent,
      exactAvailableExitSetEvent, Set.mem_setOf_eq, beta']
    constructor
    · rintro ⟨⟨hfail, hhistory⟩, hU⟩
      refine ⟨?_, hU⟩
      intro e heE
      by_cases heS : e ∈ S
      · rw [coe_incrementedBoundaryThreshold_of_mem beta delta S hdelta hupper heS]
        exact hfail e (by simpa [hU] using heS)
      · rw [coe_incrementedBoundaryThreshold_of_notMem beta delta S hdelta hupper heS]
        exact hhistory e heE
    · rintro ⟨hbox, hU⟩
      refine ⟨⟨?_, ?_⟩, hU⟩
      · intro e heU
        have heS : e ∈ S := by simpa [hU] using heU
        simpa [coe_incrementedBoundaryThreshold_of_mem beta delta S hdelta hupper heS]
          using hbox e (hSE heS)
      · intro e heE
        by_cases heS : e ∈ S
        · have h := hbox e heE
          rw [coe_incrementedBoundaryThreshold_of_mem beta delta S hdelta hupper heS] at h
          linarith
        · simpa [coe_incrementedBoundaryThreshold_of_notMem beta delta S hdelta hupper heS]
            using hbox e heE
  rw [hevent, couplingMeasure_pi_inter E (fun _e => measurableSet_Ici) hexact]
  congr 1
  apply Finset.prod_congr rfl
  intro e _he
  exact volume_restrict_Icc_Ici (beta' e)

/-- The analogous exact factorization before sprinkling. -/
theorem couplingMeasure_history_inter_exactAvailableExitSetEvent
    {iota : Type*} (E S : Finset iota) (beta : iota → I)
    (U : (iota → ℝ) → Finset iota)
    (hexact : MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    couplingMeasure iota
        (boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S) =
      (∏ e ∈ E, ENNReal.ofReal (1 - (beta e : ℝ))) *
        couplingMeasure iota (exactAvailableExitSetEvent U S) := by
  have hevent : boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S =
      (E : Set iota).pi (fun e => Set.Ici (beta e : ℝ)) ∩
        exactAvailableExitSetEvent U S := by
    ext X
    simp [boundaryClosedHistoryEvent, exactAvailableExitSetEvent, Set.mem_pi]
  rw [hevent, couplingMeasure_pi_inter E (fun _e => measurableSet_Ici) hexact]
  congr 1
  apply Finset.prod_congr rfl
  intro e _he
  exact volume_restrict_Icc_Ici (beta e)

theorem couplingMeasure_real_sprinkledFailure_inter_history_inter_exact
    {iota : Type*} [DecidableEq iota]
    (E S : Finset iota) (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota)
    (hSE : S ⊆ E) (hdelta : 0 ≤ delta)
    (hupper : ∀ e ∈ S, (beta e : ℝ) + delta ≤ 1)
    (hexact : MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    (couplingMeasure iota).real
        (sprinkledAvailableExitFailureEvent beta delta U ∩
          boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S) =
      (∏ e ∈ E,
          (1 - (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ))) *
        (couplingMeasure iota).real (exactAvailableExitSetEvent U S) := by
  rw [Measure.real,
    couplingMeasure_sprinkledFailure_inter_history_inter_exact E S beta delta U hSE
      hdelta hupper hexact,
    ENNReal.toReal_mul, ENNReal.toReal_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro e _he
  rw [ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (incrementedBoundaryThreshold beta delta S hdelta hupper e).2.2

theorem couplingMeasure_real_history_inter_exactAvailableExitSetEvent
    {iota : Type*} (E S : Finset iota) (beta : iota → I)
    (U : (iota → ℝ) → Finset iota)
    (hexact : MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    (couplingMeasure iota).real
        (boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S) =
      (∏ e ∈ E, (1 - (beta e : ℝ))) *
        (couplingMeasure iota).real (exactAvailableExitSetEvent U S) := by
  rw [Measure.real,
    couplingMeasure_history_inter_exactAvailableExitSetEvent E S beta U hexact,
    ENNReal.toReal_mul, ENNReal.toReal_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro e _he
  rw [ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (beta e).2.2

/-- Exact exit-set cells fail after sprinkling with conditional mass at most
`(1 - delta) ^ |S|`.  This theorem is deliberately ratio-free. -/
theorem couplingMeasure_real_sprinkledFailure_inter_history_inter_exact_le
    {iota : Type*} [DecidableEq iota]
    (E S : Finset iota) (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota)
    (hSE : S ⊆ E) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hupper : ∀ e ∈ S, (beta e : ℝ) + delta ≤ 1)
    (hexact : MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    (couplingMeasure iota).real
        (sprinkledAvailableExitFailureEvent beta delta U ∩
          boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S) ≤
      (1 - delta) ^ S.card *
        (couplingMeasure iota).real
          (boundaryClosedHistoryEvent E beta ∩ exactAvailableExitSetEvent U S) := by
  rw [couplingMeasure_real_sprinkledFailure_inter_history_inter_exact
      E S beta delta U hSE hdelta hupper hexact,
    couplingMeasure_real_history_inter_exactAvailableExitSetEvent E S beta U hexact]
  calc
    (∏ e ∈ E,
        (1 - (incrementedBoundaryThreshold beta delta S hdelta hupper e : ℝ))) *
          (couplingMeasure iota).real (exactAvailableExitSetEvent U S) ≤
      ((1 - delta) ^ S.card * ∏ e ∈ E, (1 - (beta e : ℝ))) *
          (couplingMeasure iota).real (exactAvailableExitSetEvent U S) :=
      mul_le_mul_of_nonneg_right
        (prod_one_sub_incrementedBoundaryThreshold_le E S hSE beta delta hdelta hdelta1
          hupper)
        (measureReal_nonneg)
    _ = (1 - delta) ^ S.card *
        ((∏ e ∈ E, (1 - (beta e : ℝ))) *
          (couplingMeasure iota).real (exactAvailableExitSetEvent U S)) := by ring

/-- Events determined by the off-boundary available-exit set remain independent of the closed
boundary history. -/
theorem couplingMeasure_real_history_inter_fewAvailableExitsEvent
    {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (beta : iota → I)
    (U : (iota → ℝ) → Finset iota) (t : ℕ)
    (hU : ∀ X, U X ⊆ E)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    (couplingMeasure iota).real
        (boundaryClosedHistoryEvent E beta ∩ fewAvailableExitsEvent U t) =
      (couplingMeasure iota).real (boundaryClosedHistoryEvent E beta) *
        (couplingMeasure iota).real (fewAvailableExitsEvent U t) := by
  have hH := measurableSet_boundaryClosedHistoryEvent_coordSigma E beta
  have hFew := measurableSet_fewAvailableExitsEvent_coordSigma E U t hU hexact
  have hindep := (indep_coordSigma_compl (E : Set iota)).indepSet_of_measurableSet hH hFew
  have heq := hindep.measure_inter_eq_mul
  rw [Measure.real, heq, ENNReal.toReal_mul, ← Measure.real, ← Measure.real]

/-- Finite-coordinate restart kernel.  Failure after sprinkling is bounded by the probability
of seeing too few available exits plus the geometric probability that all plentiful exits miss
their independent threshold increments. -/
theorem couplingMeasure_real_sprinkledFailure_inter_history_le
    {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota) (t : ℕ)
    (hU : ∀ X, U X ⊆ E)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hupper : ∀ e ∈ E, (beta e : ℝ) + delta ≤ 1)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    (couplingMeasure iota).real
        (sprinkledAvailableExitFailureEvent beta delta U ∩
          boundaryClosedHistoryEvent E beta) ≤
      ((couplingMeasure iota).real (fewAvailableExitsEvent U t) +
          (1 - delta) ^ (t + 1)) *
        (couplingMeasure iota).real (boundaryClosedHistoryEvent E beta) := by
  let mu := couplingMeasure iota
  let H := boundaryClosedHistoryEvent E beta
  let F := sprinkledAvailableExitFailureEvent beta delta U
  let C := largeAvailableExitSets E t
  let cell := fun S : Finset iota => F ∩ H ∩ exactAvailableExitSetEvent U S
  let historyCell := fun S : Finset iota => H ∩ exactAvailableExitSetEvent U S
  have hsubset : F ∩ H ⊆
      (H ∩ fewAvailableExitsEvent U t) ∪ ⋃ S ∈ C, cell S := by
    intro X hX
    by_cases hcard : (U X).card ≤ t
    · exact Or.inl ⟨hX.2, hcard⟩
    · right
      simp only [Set.mem_iUnion, cell, C, largeAvailableExitSets, Finset.mem_filter,
        Finset.mem_powerset]
      refine ⟨U X, ⟨hU X, Nat.lt_of_not_ge hcard⟩, hX.1, hX.2, rfl⟩
  have hcell : ∀ S ∈ C,
      mu.real (cell S) ≤ (1 - delta) ^ (t + 1) * mu.real (historyCell S) := by
    intro S hSC
    have hSC' := Finset.mem_filter.mp hSC
    have hSE : S ⊆ E := Finset.mem_powerset.mp hSC'.1
    have hpow : (1 - delta) ^ S.card ≤ (1 - delta) ^ (t + 1) := by
      exact pow_le_pow_of_le_one (sub_nonneg.mpr hdelta1) (sub_le_one _ hdelta)
        (Nat.succ_le_iff.mpr hSC'.2)
    calc
      mu.real (cell S) ≤ (1 - delta) ^ S.card * mu.real (historyCell S) := by
        exact couplingMeasure_real_sprinkledFailure_inter_history_inter_exact_le
          E S beta delta U hSE hdelta hdelta1 (fun e he => hupper e (hSE he))
            (hexact S hSE)
      _ ≤ (1 - delta) ^ (t + 1) * mu.real (historyCell S) :=
        mul_le_mul_of_nonneg_right hpow measureReal_nonneg
  have hhistoryPair : Set.PairwiseDisjoint (C : Set (Finset iota)) historyCell :=
    (pairwiseDisjoint_exactAvailableExitSetEvent U C).mono fun _S => Set.inter_subset_right
  have hhistoryMeas : ∀ S ∈ C, MeasurableSet (historyCell S) := by
    intro S hSC
    have hSE : S ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hSC).1
    exact (measurableSet_boundaryClosedHistoryEvent E beta).inter
      (coordSigma_le _ (exactAvailableExitSetEvent U S) (hexact S hSE))
  have hhistorySum : ∑ S ∈ C, mu.real (historyCell S) =
      mu.real (⋃ S ∈ C, historyCell S) := by
    symm
    exact measureReal_biUnion_finset hhistoryPair hhistoryMeas
  have hhistoryUnionSubset : (⋃ S ∈ C, historyCell S) ⊆ H := by
    intro X hX
    simp only [Set.mem_iUnion, historyCell] at hX
    rcases hX with ⟨S, _hSC, hXH, _hExact⟩
    exact hXH
  have hhistorySumLe : ∑ S ∈ C, mu.real (historyCell S) ≤ mu.real H := by
    rw [hhistorySum]
    exact measureReal_mono hhistoryUnionSubset (by finiteness)
  have hlarge : mu.real (⋃ S ∈ C, cell S) ≤
      (1 - delta) ^ (t + 1) * mu.real H := by
    calc
      mu.real (⋃ S ∈ C, cell S) ≤ ∑ S ∈ C, mu.real (cell S) :=
        measureReal_biUnion_finset_le C cell
      _ ≤ ∑ S ∈ C, ((1 - delta) ^ (t + 1) * mu.real (historyCell S)) :=
        Finset.sum_le_sum fun S hSC => hcell S hSC
      _ = (1 - delta) ^ (t + 1) * ∑ S ∈ C, mu.real (historyCell S) := by
        rw [Finset.mul_sum]
      _ ≤ (1 - delta) ^ (t + 1) * mu.real H :=
        mul_le_mul_of_nonneg_left hhistorySumLe (pow_nonneg (sub_nonneg.mpr hdelta1) _)
  have hlow := couplingMeasure_real_history_inter_fewAvailableExitsEvent
    E beta U t hU hexact
  calc
    mu.real (F ∩ H) ≤ mu.real
        ((H ∩ fewAvailableExitsEvent U t) ∪ ⋃ S ∈ C, cell S) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ mu.real (H ∩ fewAvailableExitsEvent U t) +
        mu.real (⋃ S ∈ C, cell S) := measureReal_union_le _ _
    _ ≤ mu.real (H ∩ fewAvailableExitsEvent U t) +
        (1 - delta) ^ (t + 1) * mu.real H := add_le_add_left hlarge _
    _ = (mu.real (fewAvailableExitsEvent U t) + (1 - delta) ^ (t + 1)) *
        mu.real H := by rw [hlow]; ring

theorem measurableSet_sprinkledAvailableExitFailureEvent {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota)
    (hU : ∀ X, U X ⊆ E)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    MeasurableSet (sprinkledAvailableExitFailureEvent beta delta U) := by
  have hevent : sprinkledAvailableExitFailureEvent beta delta U =
      ⋃ S ∈ E.powerset,
        sprinkledAvailableExitFailureEvent beta delta U ∩ exactAvailableExitSetEvent U S := by
    ext X
    simp only [Set.mem_iUnion, Finset.mem_powerset, Set.mem_inter_iff]
    constructor
    · intro hfail
      exact ⟨U X, hU X, hfail, rfl⟩
    · rintro ⟨S, _hSE, hfail, _hUS⟩
      exact hfail
  rw [hevent]
  apply MeasurableSet.biUnion_finset
  intro S hSE
  have hSE' := Finset.mem_powerset.mp hSE
  have hcell :
      sprinkledAvailableExitFailureEvent beta delta U ∩ exactAvailableExitSetEvent U S =
        (S : Set iota).pi (fun e => Set.Ici ((beta e : ℝ) + delta)) ∩
          exactAvailableExitSetEvent U S := by
    ext X
    simp only [Set.mem_inter_iff, sprinkledAvailableExitFailureEvent,
      exactAvailableExitSetEvent, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe]
    constructor
    · rintro ⟨hfail, hUS⟩
      exact ⟨fun e heS => hfail e (by simpa [hUS] using heS), hUS⟩
    · rintro ⟨hbox, hUS⟩
      exact ⟨fun e heU => hbox e (by simpa [hUS] using heU), hUS⟩
  rw [hcell]
  exact (MeasurableSet.pi S.countable_toSet fun _e _he => measurableSet_Ici).inter
    (coordSigma_le _ (exactAvailableExitSetEvent U S) (hexact S hSE'))

theorem measurableSet_sprinkledAvailableExitEvent {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (beta : iota → I) (delta : ℝ)
    (U : (iota → ℝ) → Finset iota)
    (hU : ∀ X, U X ⊆ E)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    MeasurableSet (sprinkledAvailableExitEvent beta delta U) := by
  rw [← sprinkledAvailableExitFailureEvent_eq_compl beta delta U, measurableSet_compl_iff]
  exact measurableSet_sprinkledAvailableExitFailureEvent E beta delta U hU hexact

/-- Strict ratio-free form of the restart estimate.  The hypotheses expose the only geometric
input still needed for Grimmett's Lemma 7.17: the off-boundary available-exit set is rarely
small. -/
theorem sprinkledAvailableExit_inter_history_gt
    {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (beta : iota → I) (delta epsilon : ℝ)
    (U : (iota → ℝ) → Finset iota) (t : ℕ)
    (hU : ∀ X, U X ⊆ E)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hupper : ∀ e ∈ E, (beta e : ℝ) + delta ≤ 1)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S))
    (hsmall : (couplingMeasure iota).real (fewAvailableExitsEvent U t) +
      (1 - delta) ^ (t + 1) < epsilon) :
    (1 - epsilon) *
        (couplingMeasure iota).real (boundaryClosedHistoryEvent E beta) <
      (couplingMeasure iota).real
        (sprinkledAvailableExitEvent beta delta U ∩
          boundaryClosedHistoryEvent E beta) := by
  let mu := couplingMeasure iota
  let H := boundaryClosedHistoryEvent E beta
  let success := sprinkledAvailableExitEvent beta delta U
  let failure := sprinkledAvailableExitFailureEvent beta delta U
  have hHpos : 0 < mu.real H := by
    apply couplingMeasure_real_boundaryClosedHistoryEvent_pos
    intro e heE
    have := hupper e heE
    linarith
  have hfail := couplingMeasure_real_sprinkledFailure_inter_history_le
    E beta delta U t hU hdelta.le hdelta1 hupper hexact
  have hfailLt : mu.real (failure ∩ H) < epsilon * mu.real H :=
    hfail.trans_lt (mul_lt_mul_of_pos_right hsmall hHpos)
  have hsuccessMeas : MeasurableSet success :=
    measurableSet_sprinkledAvailableExitEvent E beta delta U hU hexact
  have hfailureMeas : MeasurableSet failure :=
    measurableSet_sprinkledAvailableExitFailureEvent E beta delta U hU hexact
  have hpartition : (success ∩ H) ∪ (failure ∩ H) = H := by
    rw [sprinkledAvailableExitFailureEvent_eq_compl]
    ext X
    simp [success, failure]
  have hdisjoint : Disjoint (success ∩ H) (failure ∩ H) := by
    rw [sprinkledAvailableExitFailureEvent_eq_compl]
    exact Set.disjoint_left.2 fun _X hX hX' => hX'.1 hX.1
  have hsum : mu.real (success ∩ H) + mu.real (failure ∩ H) = mu.real H := by
    rw [← measureReal_union hdisjoint (hfailureMeas.inter
      (measurableSet_boundaryClosedHistoryEvent E beta)), hpartition]
  dsimp [mu, H, success, failure] at hsum hfailLt ⊢
  linarith

/-- Conditional-probability form of the restart estimate.  Unlike a totalized definition, this
corollary divides only after the history mass has been proved positive. -/
theorem sprinkledAvailableExit_conditionalProbability_gt
    {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (beta : iota → I) (delta epsilon : ℝ)
    (U : (iota → ℝ) → Finset iota) (t : ℕ)
    (hU : ∀ X, U X ⊆ E)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hupper : ∀ e ∈ E, (beta e : ℝ) + delta ≤ 1)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S))
    (hsmall : (couplingMeasure iota).real (fewAvailableExitsEvent U t) +
      (1 - delta) ^ (t + 1) < epsilon) :
    1 - epsilon <
      (couplingMeasure iota).real
          (sprinkledAvailableExitEvent beta delta U ∩
            boundaryClosedHistoryEvent E beta) /
        (couplingMeasure iota).real (boundaryClosedHistoryEvent E beta) := by
  have hHpos : 0 < (couplingMeasure iota).real (boundaryClosedHistoryEvent E beta) := by
    apply couplingMeasure_real_boundaryClosedHistoryEvent_pos
    intro e heE
    have := hupper e heE
    linarith
  exact (lt_div_iff₀ hHpos).2
    (sprinkledAvailableExit_inter_history_gt E beta delta epsilon U t hU hdelta hdelta1
      hupper hexact hsmall)

/-! ### The closed-exit uncertainty bound (equation 7.22) -/

/-- On an exact available-exit cell `S`, the probability that every exit is `p`-closed is
exactly `(1-p)^|S|`.  The auxiliary zero-threshold history has probability one under the
uniform coupling and lets this statement reuse the heterogeneous box factorization above. -/
theorem couplingMeasure_real_allAvailableExitsClosed_inter_zeroHistory_inter_exact
    {iota : Type*} [DecidableEq iota]
    (E S : Finset iota) (p : I) (U : (iota → ℝ) → Finset iota)
    (hSE : S ⊆ E)
    (hexact : MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    (couplingMeasure iota).real
        (sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (p : ℝ) U ∩
          boundaryClosedHistoryEvent E (fun _ => (0 : I)) ∩
          exactAvailableExitSetEvent U S) =
      (1 - (p : ℝ)) ^ S.card *
        (couplingMeasure iota).real (exactAvailableExitSetEvent U S) := by
  rw [couplingMeasure_real_sprinkledFailure_inter_history_inter_exact
    E S (fun _ => (0 : I)) (p : ℝ) U hSE p.2.1 (fun _ _ => p.2.2) hexact]
  congr 1
  calc
    (∏ e ∈ E,
        (1 - (incrementedBoundaryThreshold (fun _ => (0 : I)) (p : ℝ) S
          p.2.1 (fun _ _ => p.2.2) e : ℝ))) =
        ∏ e ∈ S,
          (1 - (incrementedBoundaryThreshold (fun _ => (0 : I)) (p : ℝ) S
            p.2.1 (fun _ _ => p.2.2) e : ℝ)) := by
      symm
      apply Finset.prod_subset hSE
      intro e _heE heS
      simp [coe_incrementedBoundaryThreshold_of_notMem _ _ _ _ _ heS]
    _ = ∏ _e ∈ S, (1 - (p : ℝ)) := by
      apply Finset.prod_congr rfl
      intro e heS
      rw [coe_incrementedBoundaryThreshold_of_mem _ _ _ _ _ heS]
    _ = (1 - (p : ℝ)) ^ S.card := by simp

/-- Equation (7.22), abstracted from the geometry: if the available set is determined off the
finite boundary `E`, then on the event `|U| ≤ t` there remains at least `(1-p)^t` of closed-exit
uncertainty. -/
theorem one_sub_pow_mul_fewAvailableExits_le_allAvailableExitsClosed
    {iota : Type*} [DecidableEq iota]
    (E : Finset iota) (p : I) (U : (iota → ℝ) → Finset iota) (t : ℕ)
    (hU : ∀ X, U X ⊆ E)
    (hexact : ∀ S ⊆ E, MeasurableSet[coordSigma iota ((E : Set iota)ᶜ)]
      (exactAvailableExitSetEvent U S)) :
    (1 - (p : ℝ)) ^ t *
        (couplingMeasure iota).real (fewAvailableExitsEvent U t) ≤
      (couplingMeasure iota).real
        (sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (p : ℝ) U ∩
          boundaryClosedHistoryEvent E (fun _ => (0 : I))) := by
  let C := E.powerset.filter fun S => S.card ≤ t
  let cell := fun S : Finset iota =>
    sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (p : ℝ) U ∩
      boundaryClosedHistoryEvent E (fun _ => (0 : I)) ∩ exactAvailableExitSetEvent U S
  have hcellMeas : ∀ S ∈ C, MeasurableSet (cell S) := by
    intro S hSC
    have hSE := Finset.mem_powerset.mp (Finset.mem_filter.mp hSC).1
    -- The left side of the exact factorization is measurable as a finite box intersected with
    -- the off-boundary cell; use the event identity from its proof directly.
    let beta' := incrementedBoundaryThreshold (fun _ => (0 : I)) (p : ℝ) S
      p.2.1 (fun _ _ => p.2.2)
    have hrepr : cell S =
        (E : Set iota).pi (fun e => Set.Ici (beta' e : ℝ)) ∩
          exactAvailableExitSetEvent U S := by
      ext X
      simp only [cell, Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe,
        sprinkledAvailableExitFailureEvent, boundaryClosedHistoryEvent,
        exactAvailableExitSetEvent, Set.mem_setOf_eq, beta']
      constructor
      · rintro ⟨⟨hfail, hzero⟩, hUS⟩
        refine ⟨?_, hUS⟩
        intro e heE
        by_cases heS : e ∈ S
        · rw [coe_incrementedBoundaryThreshold_of_mem]
          exact hfail e (by simpa [hUS] using heS)
        · rw [coe_incrementedBoundaryThreshold_of_notMem _ _ _ _ _ heS]
          exact hzero e heE
      · rintro ⟨hbox, hUS⟩
        refine ⟨⟨?_, ?_⟩, hUS⟩
        · intro e heU
          have heS : e ∈ S := by simpa [hUS] using heU
          simpa [coe_incrementedBoundaryThreshold_of_mem _ _ _ _ _ heS]
            using hbox e (hSE heS)
        · intro e heE
          by_cases heS : e ∈ S
          · have h := hbox e heE
            rw [coe_incrementedBoundaryThreshold_of_mem _ _ _ _ _ heS] at h
            exact le_trans (by exact_mod_cast p.2.1) h
          · simpa [coe_incrementedBoundaryThreshold_of_notMem _ _ _ _ _ heS]
              using hbox e heE
    rw [hrepr]
    exact (MeasurableSet.pi E.countable_toSet fun _e _he => measurableSet_Ici).inter
      (coordSigma_le _ (exactAvailableExitSetEvent U S) (hexact S hSE))
  have hpair : Set.PairwiseDisjoint (C : Set (Finset iota)) cell :=
    (pairwiseDisjoint_exactAvailableExitSetEvent U C).mono fun _S =>
      Set.inter_subset_right.trans Set.inter_subset_right
  have hfewEq : fewAvailableExitsEvent U t =
      ⋃ S ∈ C, exactAvailableExitSetEvent U S := by
    ext X
    simp only [fewAvailableExitsEvent, Set.mem_setOf_eq, Set.mem_iUnion, C,
      Finset.mem_filter, Finset.mem_powerset, exactAvailableExitSetEvent]
    constructor
    · intro hcard
      exact ⟨U X, ⟨hU X, hcard⟩, rfl⟩
    · rintro ⟨S, ⟨_hSE, hcard⟩, hUS⟩
      simpa [hUS] using hcard
  have hexactPair := pairwiseDisjoint_exactAvailableExitSetEvent U C
  have hexactMeas : ∀ S ∈ C, MeasurableSet (exactAvailableExitSetEvent U S) := by
    intro S hSC
    have hSE := Finset.mem_powerset.mp (Finset.mem_filter.mp hSC).1
    exact coordSigma_le _ _ (hexact S hSE)
  have hfewSum : (couplingMeasure iota).real (fewAvailableExitsEvent U t) =
      ∑ S ∈ C, (couplingMeasure iota).real (exactAvailableExitSetEvent U S) := by
    rw [hfewEq]
    exact measureReal_biUnion_finset hexactPair hexactMeas
  have hunionSubset : (⋃ S ∈ C, cell S) ⊆
      sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (p : ℝ) U ∩
        boundaryClosedHistoryEvent E (fun _ => (0 : I)) := by
    intro X hX
    simp only [Set.mem_iUnion, cell] at hX
    rcases hX with ⟨S, _hSC, hfail, hzero, _hexact⟩
    exact ⟨hfail, hzero⟩
  rw [hfewSum, Finset.mul_sum]
  calc
    ∑ S ∈ C, (1 - (p : ℝ)) ^ t *
        (couplingMeasure iota).real (exactAvailableExitSetEvent U S) ≤
      ∑ S ∈ C, (couplingMeasure iota).real (cell S) := by
        apply Finset.sum_le_sum
        intro S hSC
        have hdata := Finset.mem_filter.mp hSC
        have hSE := Finset.mem_powerset.mp hdata.1
        rw [couplingMeasure_real_allAvailableExitsClosed_inter_zeroHistory_inter_exact
          E S p U hSE (hexact S hSE)]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (sub_nonneg.mpr p.2.2)
            (sub_le_one _ p.2.1) hdata.2) measureReal_nonneg
    _ = (couplingMeasure iota).real (⋃ S ∈ C, cell S) := by
      symm
      exact measureReal_biUnion_finset hpair hcellMeas
    _ ≤ (couplingMeasure iota).real
        (sprinkledAvailableExitFailureEvent (fun _ => (0 : I)) (p : ℝ) U ∩
          boundaryClosedHistoryEvent E (fun _ => (0 : I))) :=
      measureReal_mono hunionSubset (by finiteness)

end Percolation
