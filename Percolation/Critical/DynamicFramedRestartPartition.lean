import Percolation.Critical.DynamicFramedRestart
import Percolation.Critical.DynamicRevealCells
import Percolation.Critical.BlockSuccessComposition

/-!
# Finite partitions of fully framed dynamic restarts

The source construction on pp. 159--162 chooses both a signed exit direction and a transverse
sign mask.  `PartitionedOrientedRestartStage` cannot represent the latter.  This file supplies
the corresponding finite partition with `FramedRestartQuery` as its literal query type.  Its
probability proof is the same null-safe cell summation, but now uses the full-frame form of
Lemma 7.17.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace AdaptiveSiteExploration

variable {V C : Type*}

/-- One source-faithful random-region restart stage, including its transverse steering mask. -/
structure PartitionedFramedRestartStage
    (d : ℕ) (C : Type*) [DecidableEq C]
    (m n : ℕ) (p : I) (delta epsilon : ℝ) where
  cells : Finset C
  query : C → FramedRestartQuery d
  pastSupport : C → Finset (CubicEdge d)
  past : C → Set (CubicEdge d → ℝ)
  past_measurable : ∀ c ∈ cells,
    MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c)
  fresh : ∀ c ∈ cells,
    Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d))
  pairwise_cells : Set.PairwiseDisjoint (cells : Set C) fun c ↦
    past c ∩ (query c).boundaryHistoryEvent n
  restart_gt : ∀ c ∈ cells,
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
      (couplingMeasure (CubicEdge d)).real
        ((query c).successEvent m n p delta ∩
          (query c).boundaryHistoryEvent n)

namespace PartitionedFramedRestartStage

variable {d m n : ℕ} {p : I} {delta epsilon : ℝ} [DecidableEq C]
    (S : PartitionedFramedRestartStage d C m n p delta epsilon)

/-- Exact framed reveal cell, including closure of the boundary at its current thresholds. -/
def cell (c : C) : Set (CubicEdge d → ℝ) :=
  S.past c ∩ (S.query c).boundaryHistoryEvent n

/-- Successful part of one framed reveal cell. -/
def successfulCell (c : C) : Set (CubicEdge d → ℝ) :=
  (S.query c).successEvent m n p delta ∩ S.cell c

/-- History slice partitioned by this stage. -/
def cellUnion : Set (CubicEdge d → ℝ) :=
  ⋃ c ∈ S.cells, S.cell c

/-- Single Boolean success event exposed by the fully framed stage. -/
def successEvent : Set (CubicEdge d → ℝ) :=
  ⋃ c ∈ S.cells, S.successfulCell c

theorem measurableSet_cell (c : C) (hc : c ∈ S.cells) :
    MeasurableSet (S.cell c) := by
  have hpast : MeasurableSet (S.past c) :=
    (coordSigma_le _) _ (S.past_measurable c hc)
  have hboundary : MeasurableSet ((S.query c).boundaryHistoryEvent n) :=
    (coordSigma_le _) _
      (measurableSet_framedBoundaryClosedHistoryEvent_coordSigma
        (S.query c).center (S.query c).direction (S.query c).transverseFlip
        (S.query c).region n (S.query c).beta)
  exact hpast.inter hboundary

theorem measurableSet_successfulCell (c : C) (hc : c ∈ S.cells) :
    MeasurableSet (S.successfulCell c) := by
  have hsuccess : MeasurableSet ((S.query c).successEvent m n p delta) :=
    (coordSigma_le _) _ ((S.query c).measurableSet_successEvent_coordSigma m n p delta)
  exact hsuccess.inter (S.measurableSet_cell c hc)

theorem measurableSet_successEvent : MeasurableSet S.successEvent := by
  apply MeasurableSet.biUnion S.cells.countable_toSet
  intro c hc
  exact S.measurableSet_successfulCell c hc

theorem successfulCell_subset_cell (c : C) : S.successfulCell c ⊆ S.cell c :=
  Set.inter_subset_right

theorem successEvent_subset_cellUnion : S.successEvent ⊆ S.cellUnion := by
  intro X hX
  simp only [successEvent, Set.mem_iUnion] at hX
  obtain ⟨c, hc, hsuccess⟩ := hX
  exact Set.mem_iUnion_of_mem c <| Set.mem_iUnion_of_mem hc
    (S.successfulCell_subset_cell c hsuccess)

/-- Semantic reading of a finite exact-cell stage: on the outer history, the successful union
is precisely the success event belonging to the cell actually realized by the configuration. -/
theorem successEvent_eq_semantic_of_exactRealization
    [Fintype C]
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (hcells : S.cells = Finset.univ)
    (hcell : ∀ c, S.cell c = exactRevealCellEvent history realizedCell c) :
    S.successEvent =
      {X | X ∈ history ∧
        X ∈ (S.query (realizedCell X)).successEvent m n p delta} := by
  ext X
  simp only [successEvent, successfulCell, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, hsuccess, hXcell⟩
    have hcUniv : c ∈ (Finset.univ : Finset C) := by simpa [hcells] using hc
    have hExact : X ∈ exactRevealCellEvent history realizedCell c := by
      simpa [hcell c] using hXcell
    have hrealized : realizedCell X = c := hExact.2
    exact ⟨hExact.1, by simpa [hrealized] using hsuccess⟩
  · rintro ⟨hXhistory, hsuccess⟩
    refine ⟨realizedCell X, ?_, hsuccess, ?_⟩
    · simpa [hcells]
    · rw [hcell]
      exact ⟨hXhistory, rfl⟩

/-- Cellwise framed Lemma 7.17 bounds sum to one null-safe stage bound. -/
theorem success_lower_bound :
    (1 - epsilon) *
        (couplingMeasure (CubicEdge d)).real S.cellUnion ≤
      (couplingMeasure (CubicEdge d)).real S.successEvent := by
  apply mul_measureReal_le_partitionedSuccess S.cells S.cell S.successfulCell
    S.cellUnion (1 - epsilon) rfl S.pairwise_cells
  · exact S.measurableSet_cell
  · exact S.measurableSet_successfulCell
  · intro c _hc
    exact S.successfulCell_subset_cell c
  · intro c hc
    simpa only [successfulCell, cell, Set.inter_assoc] using
      framedSprinkledRestart_inter_past_history_ge
        (S.query c).center (S.query c).direction (S.query c).transverseFlip
        (S.query c).region p (S.query c).beta delta epsilon
        (S.pastSupport c) (S.past c) (S.past_measurable c hc)
        (S.fresh c hc) (S.restart_gt c hc)

/-- A framed stage may be composed through a probability-one coupling support without forcing
its finite cell union to equal the semantic event literally on junk label realizations.  This
is the stage-specific-cell analogue of the exact-history interface used by the earlier dynamic
programs. -/
theorem success_lower_bound_of_inter_support_eq
    (support outer next : Set (CubicEdge d → ℝ))
    (hsupport : MeasurableSet support)
    (hsupport_one : (couplingMeasure (CubicEdge d)).real support = 1)
    (houter : S.cellUnion ∩ support = outer ∩ support)
    (hnext : S.successEvent ∩ support = next ∩ support) :
    (1 - epsilon) * (couplingMeasure (CubicEdge d)).real outer ≤
      (couplingMeasure (CubicEdge d)).real next := by
  let μ := couplingMeasure (CubicEdge d)
  calc
    (1 - epsilon) * μ.real outer =
        (1 - epsilon) * μ.real (outer ∩ support) := by
      rw [measureReal_inter_eq_of_measureReal_eq_one support outer hsupport hsupport_one]
    _ = (1 - epsilon) * μ.real (S.cellUnion ∩ support) := by rw [houter]
    _ = (1 - epsilon) * μ.real S.cellUnion := by
      rw [measureReal_inter_eq_of_measureReal_eq_one
        support S.cellUnion hsupport hsupport_one]
    _ ≤ μ.real S.successEvent := S.success_lower_bound
    _ = μ.real (S.successEvent ∩ support) := by
      rw [measureReal_inter_eq_of_measureReal_eq_one
        support S.successEvent hsupport hsupport_one]
    _ = μ.real (next ∩ support) := by rw [hnext]
    _ = μ.real next :=
      measureReal_inter_eq_of_measureReal_eq_one support next hsupport hsupport_one

end PartitionedFramedRestartStage

/-- Event family of a history-indexed program of fully framed stages. -/
def finitePartitionedFramedRestartStageFamily
    {d : ℕ} [DecidableEq C] {m n : ℕ} {p : I} {delta epsilon : ℝ}
    (stage : List (V × Bool) → V → ℕ →
      PartitionedFramedRestartStage d C m n p delta epsilon) :
    List (V × Bool) → V → ℕ → Set (CubicEdge d → ℝ) :=
  fun history v j ↦ (stage history v j).successEvent

section Constructors

variable [Fintype C] [DecidableEq C]

/-- Build a framed partition from an exact finite realization. -/
noncomputable def PartitionedFramedRestartStage.ofFiniteRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (pastSupport : C → Finset (CubicEdge d))
    (past : C → Set (CubicEdge d → ℝ))
    (hpast : ∀ c, MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c))
    (hfresh : ∀ c, Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d)))
    (hcell : ∀ c, past c ∩ (query c).boundaryHistoryEvent n =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon where
  cells := Finset.univ
  query := query
  pastSupport := pastSupport
  past := past
  past_measurable := fun c _hc ↦ hpast c
  fresh := fun c _hc ↦ hfresh c
  pairwise_cells := by
    intro c hc c' hc' hcc'
    change Disjoint (past c ∩ (query c).boundaryHistoryEvent n)
      (past c' ∩ (query c').boundaryHistoryEvent n)
    rw [hcell c, hcell c']
    exact pairwiseDisjoint_exactRevealCellEvent Finset.univ history realizedCell
      (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc') hcc'
  restart_gt := fun c _hc ↦ hrestart c

theorem PartitionedFramedRestartStage.cellUnion_ofFiniteRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (pastSupport : C → Finset (CubicEdge d))
    (past : C → Set (CubicEdge d → ℝ))
    (hpast : ∀ c, MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c))
    (hfresh : ∀ c, Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d)))
    (hcell : ∀ c, past c ∩ (query c).boundaryHistoryEvent n =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofFiniteRealization history realizedCell query
      pastSupport past hpast hfresh hcell hrestart).cellUnion = history := by
  rw [PartitionedFramedRestartStage.cellUnion]
  change (⋃ c ∈ (Finset.univ : Finset C),
    past c ∩ (query c).boundaryHistoryEvent n) = history
  simp_rw [hcell]
  exact biUnion_univ_exactRevealCellEvent history realizedCell

/-- Filter impossible indices while retaining every actually realized framed cell. -/
noncomputable def PartitionedFramedRestartStage.ofFiniteValidRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (valid : C → Prop) [DecidablePred valid]
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → FramedRestartQuery d)
    (pastSupport : C → Finset (CubicEdge d))
    (past : C → Set (CubicEdge d → ℝ))
    (hpast : ∀ c, valid c → MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c))
    (hfresh : ∀ c, valid c → Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d)))
    (hcell : ∀ c, valid c → past c ∩ (query c).boundaryHistoryEvent n =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c, valid c →
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    PartitionedFramedRestartStage d C m n p delta epsilon where
  cells := Finset.univ.filter valid
  query := query
  pastSupport := pastSupport
  past := past
  past_measurable := fun c hc ↦ hpast c (Finset.mem_filter.mp hc).2
  fresh := fun c hc ↦ hfresh c (Finset.mem_filter.mp hc).2
  pairwise_cells := by
    intro c hc c' hc' hcc'
    change Disjoint (past c ∩ (query c).boundaryHistoryEvent n)
      (past c' ∩ (query c').boundaryHistoryEvent n)
    rw [hcell c (Finset.mem_filter.mp hc).2,
      hcell c' (Finset.mem_filter.mp hc').2]
    exact pairwiseDisjoint_exactRevealCellEvent (Finset.univ.filter valid)
      history realizedCell (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc') hcc'
  restart_gt := fun c hc ↦ hrestart c (Finset.mem_filter.mp hc).2

theorem PartitionedFramedRestartStage.cellUnion_ofFiniteValidRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (valid : C → Prop) [DecidablePred valid]
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (hvalid : ∀ X ∈ history, valid (realizedCell X))
    (query : C → FramedRestartQuery d)
    (pastSupport : C → Finset (CubicEdge d))
    (past : C → Set (CubicEdge d → ℝ))
    (hpast : ∀ c, valid c → MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c))
    (hfresh : ∀ c, valid c → Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d)))
    (hcell : ∀ c, valid c → past c ∩ (query c).boundaryHistoryEvent n =
      exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c, valid c →
      (1 - epsilon) * (couplingMeasure (CubicEdge d)).real
          ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    (PartitionedFramedRestartStage.ofFiniteValidRealization valid history realizedCell
      query pastSupport past hpast hfresh hcell hrestart).cellUnion = history := by
  rw [PartitionedFramedRestartStage.cellUnion]
  change (⋃ c ∈ Finset.univ.filter valid,
    past c ∩ (query c).boundaryHistoryEvent n) = history
  calc
    (⋃ c ∈ Finset.univ.filter valid,
        past c ∩ (query c).boundaryHistoryEvent n) =
        ⋃ c ∈ Finset.univ.filter valid,
          exactRevealCellEvent history realizedCell c := by
      apply Set.iUnion_congr
      intro c
      apply Set.iUnion_congr
      intro hc
      exact hcell c (Finset.mem_filter.mp hc).2
    _ = history := biUnion_filter_exactRevealCellEvent valid history realizedCell hvalid

end Constructors

end AdaptiveSiteExploration

end Percolation
