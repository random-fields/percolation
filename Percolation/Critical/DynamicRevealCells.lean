import Percolation.Critical.DynamicRestartPartition

/-!
# Finite reveal-cell indices for the Grimmett--Marstrand construction

An exact dynamic-restart cell records two finite pieces of data: the explored vertex region
inside the restart box and, on every coordinate that the restart can read, the number of earlier
sprinkling increments charged to that edge.  The source overlap bound is `2d+1`, so multiplicity
is stored in `Fin (2d+2)`.  This makes the space of possible reveal cells genuinely finite and
allows later probability arguments to sum over it.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-! ## Exact finite reveal fibers -/

/-- The part of `history` on which a finite reveal algorithm returns the exact cell `c`. -/
def exactRevealCellEvent {Omega C : Type*}
    (history : Set Omega) (realizedCell : Omega → C) (c : C) : Set Omega :=
  history ∩ {omega | realizedCell omega = c}

theorem pairwiseDisjoint_exactRevealCellEvent
    {Omega C : Type*} [DecidableEq C]
    (cells : Finset C) (history : Set Omega) (realizedCell : Omega → C) :
    Set.PairwiseDisjoint (cells : Set C)
      (exactRevealCellEvent history realizedCell) := by
  intro c _hc c' _hc' hcc'
  change Disjoint (exactRevealCellEvent history realizedCell c)
    (exactRevealCellEvent history realizedCell c')
  rw [Set.disjoint_left]
  intro omega homega homega'
  exact hcc' (homega.2.symm.trans homega'.2)

theorem iUnion_exactRevealCellEvent
    {Omega C : Type*} [Fintype C]
    (history : Set Omega) (realizedCell : Omega → C) :
    (⋃ c : C, exactRevealCellEvent history realizedCell c) = history := by
  ext omega
  simp [exactRevealCellEvent]

theorem biUnion_univ_exactRevealCellEvent
    {Omega C : Type*} [Fintype C]
    (history : Set Omega) (realizedCell : Omega → C) :
    (⋃ c ∈ (Finset.univ : Finset C), exactRevealCellEvent history realizedCell c) =
      history := by
  simpa using iUnion_exactRevealCellEvent history realizedCell

theorem measurableSet_exactRevealCellEvent
    {Omega C : Type*} [MeasurableSpace Omega]
    {history : Set Omega} {realizedCell : Omega → C}
    (hHistory : MeasurableSet history)
    (hFiber : ∀ c, MeasurableSet {omega | realizedCell omega = c}) (c : C) :
    MeasurableSet (exactRevealCellEvent history realizedCell c) :=
  hHistory.inter (hFiber c)

/-- If every realized cell satisfies a decidable validity predicate, filtering the finite cell
space to valid indices still covers the whole history. -/
theorem biUnion_filter_exactRevealCellEvent
    {Omega C : Type*} [Fintype C] [DecidableEq C]
    (valid : C → Prop) [DecidablePred valid]
    (history : Set Omega) (realizedCell : Omega → C)
    (hvalid : ∀ omega ∈ history, valid (realizedCell omega)) :
    (⋃ c ∈ (Finset.univ.filter valid), exactRevealCellEvent history realizedCell c) =
      history := by
  ext omega
  constructor
  · intro h
    simp only [Set.mem_iUnion, exactRevealCellEvent, Set.mem_inter_iff,
      Set.mem_setOf_eq] at h
    obtain ⟨c, _hc, hhistory, _hcell⟩ := h
    exact hhistory
  · intro hhistory
    apply Set.mem_iUnion_of_mem (realizedCell omega)
    apply Set.mem_iUnion_of_mem (by simpa using hvalid omega hhistory)
    exact ⟨hhistory, rfl⟩

/-- Vertices available to an explored restart region. -/
abbrev RestartBoxVertex (d n : ℕ) :=
  {x : Cubic d // x ∈ cubicMetricBox d cubicOrigin n}

/-- Edge coordinates on which a reference restart can depend. -/
abbrev RestartSupportCoordinate (d : ℕ) (i : Fin d) (m n : ℕ) :=
  {e : CubicEdge d // e ∈ seedConnectionSupport d i m n}

noncomputable instance restartBoxVertexFintype (d n : ℕ) :
    Fintype (RestartBoxVertex d n) :=
  Fintype.ofFinite _

noncomputable instance restartSupportCoordinateFintype
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    Fintype (RestartSupportCoordinate d i m n) :=
  Fintype.ofFinite _

/-- Finite data selecting one possible random explored region and accumulated threshold profile
for a reference restart in direction `i`. -/
structure RestartRevealCellIndex (d : ℕ) (i : Fin d) (m n : ℕ) where
  region : Finset (RestartBoxVertex d n)
  multiplicity : RestartSupportCoordinate d i m n → Fin (2 * d + 2)

noncomputable instance restartRevealCellIndexDecidableEq
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    DecidableEq (RestartRevealCellIndex d i m n) :=
  Classical.decEq _

/-- A reveal-cell index is just a pair of finite objects; this equivalence supplies the concrete
finiteness instance without postulating finiteness of a structure with a function field. -/
def restartRevealCellIndexEquiv
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    RestartRevealCellIndex d i m n ≃
      Finset (RestartBoxVertex d n) ×
        (RestartSupportCoordinate d i m n → Fin (2 * d + 2)) where
  toFun c := (c.region, c.multiplicity)
  invFun data := ⟨data.1, data.2⟩
  left_inv c := by cases c; rfl
  right_inv data := by cases data; rfl

noncomputable instance restartRevealCellIndexFintype
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    Fintype (RestartRevealCellIndex d i m n) :=
  Fintype.ofEquiv
    (Finset (RestartBoxVertex d n) ×
      (RestartSupportCoordinate d i m n → Fin (2 * d + 2)))
    (restartRevealCellIndexEquiv d i m n).symm

namespace RestartRevealCellIndex

variable {d m n : ℕ} {i : Fin d}

/-- Ambient cubic vertices of the cell's explored region. -/
noncomputable def regionVertices (c : RestartRevealCellIndex d i m n) :
    Finset (Cubic d) :=
  c.region.map (Function.Embedding.subtype _)

@[simp]
theorem mem_regionVertices_iff (c : RestartRevealCellIndex d i m n) (x : Cubic d) :
    x ∈ c.regionVertices ↔
      ∃ hx : x ∈ cubicMetricBox d cubicOrigin n, (⟨x, hx⟩ : RestartBoxVertex d n) ∈ c.region := by
  classical
  simp [regionVertices]

theorem regionVertices_subset_box (c : RestartRevealCellIndex d i m n) :
    c.regionVertices ⊆ cubicMetricBox d cubicOrigin n := by
  intro x hx
  obtain ⟨hbox, _⟩ := (c.mem_regionVertices_iff x).mp hx
  exact hbox

/-- Multiplicity on every cubic edge, extended by zero away from the finite restart support. -/
noncomputable def edgeMultiplicity
    (c : RestartRevealCellIndex d i m n) (e : CubicEdge d) : ℕ :=
  if he : e ∈ seedConnectionSupport d i m n then c.multiplicity ⟨e, he⟩ else 0

theorem edgeMultiplicity_le (c : RestartRevealCellIndex d i m n) (e : CubicEdge d) :
    c.edgeMultiplicity e ≤ 2 * d + 1 := by
  classical
  unfold edgeMultiplicity
  split
  · have hlt := (c.multiplicity ⟨e, ‹_›⟩).isLt
    omega
  · omega

@[simp]
theorem edgeMultiplicity_of_notMem
    (c : RestartRevealCellIndex d i m n) {e : CubicEdge d}
    (he : e ∉ seedConnectionSupport d i m n) :
    c.edgeMultiplicity e = 0 := by
  simp [edgeMultiplicity, he]

/-- Heterogeneous boundary threshold represented by the reveal cell.  The hypotheses expose the
entire source budget: a nonnegative base density and increment, with `2d+1` increments still at
most one. -/
noncomputable def thresholdProfile
    (c : RestartRevealCellIndex d i m n) (base delta : ℝ)
    (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1) : CubicEdge d → I :=
  fun e =>
    ⟨base + c.edgeMultiplicity e * delta,
      add_nonneg hbase (mul_nonneg (Nat.cast_nonneg _) hdelta),
      (by
        calc
          base + c.edgeMultiplicity e * delta ≤
              base + (2 * d + 1 : ℕ) * delta := by
            gcongr
            exact_mod_cast c.edgeMultiplicity_le e
          _ ≤ 1 := hupper)⟩

@[simp]
theorem coe_thresholdProfile
    (c : RestartRevealCellIndex d i m n) (base delta : ℝ)
    (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1) (e : CubicEdge d) :
    (c.thresholdProfile base delta hbase hdelta hupper e : ℝ) =
      base + c.edgeMultiplicity e * delta :=
  rfl

theorem thresholdProfile_le_globalBudget
    (c : RestartRevealCellIndex d i m n) (base delta budget : ℝ)
    (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1)
    (hbudget : base + (2 * d + 1 : ℕ) * delta ≤ budget)
    (e : CubicEdge d) :
    (c.thresholdProfile base delta hbase hdelta hupper e : ℝ) ≤ budget := by
  rw [coe_thresholdProfile]
  have hmult : (c.edgeMultiplicity e : ℝ) ≤ (2 * d + 1 : ℕ) := by
    exact_mod_cast c.edgeMultiplicity_le e
  calc
    base + c.edgeMultiplicity e * delta ≤
        base + (2 * d + 1 : ℕ) * delta := by
      gcongr
    _ ≤ budget := hbudget

/-- Source-specialized threshold profile starting at `p_c+η/2` and charging one of at most
`2d+1` increments to every edge. -/
noncomputable def dynamicThresholdProfile
    (c : RestartRevealCellIndex d i m n) (pc eta : ℝ)
    (hpc : 0 ≤ pc) (heta : 0 ≤ eta) (htotal : pc + eta ≤ 1) :
    CubicEdge d → I :=
  c.thresholdProfile (dynamicBlockBaseDensity pc eta)
    (dynamicBlockIncrement d eta)
    (by unfold dynamicBlockBaseDensity; positivity)
    (by unfold dynamicBlockIncrement; positivity)
    (by rw [dynamicBlockBaseDensity_add_maxIncrement]; exact htotal)

@[simp]
theorem coe_dynamicThresholdProfile
    (c : RestartRevealCellIndex d i m n) (pc eta : ℝ)
    (hpc : 0 ≤ pc) (heta : 0 ≤ eta) (htotal : pc + eta ≤ 1)
    (e : CubicEdge d) :
    (c.dynamicThresholdProfile pc eta hpc heta htotal e : ℝ) =
      dynamicBlockBaseDensity pc eta +
        c.edgeMultiplicity e * dynamicBlockIncrement d eta :=
  rfl

theorem dynamicThresholdProfile_le
    (c : RestartRevealCellIndex d i m n) (pc eta : ℝ)
    (hpc : 0 ≤ pc) (heta : 0 ≤ eta) (htotal : pc + eta ≤ 1)
    (e : CubicEdge d) :
    (c.dynamicThresholdProfile pc eta hpc heta htotal e : ℝ) ≤ pc + eta := by
  have hbase : 0 ≤ dynamicBlockBaseDensity pc eta := by
    unfold dynamicBlockBaseDensity
    positivity
  have hdelta : 0 ≤ dynamicBlockIncrement d eta := by
    unfold dynamicBlockIncrement
    positivity
  have hmax : dynamicBlockBaseDensity pc eta +
      (2 * d + 1 : ℕ) * dynamicBlockIncrement d eta ≤ 1 := by
    rw [dynamicBlockBaseDensity_add_maxIncrement]
    exact htotal
  have hbudget : dynamicBlockBaseDensity pc eta +
      (2 * d + 1 : ℕ) * dynamicBlockIncrement d eta ≤ pc + eta := by
    rw [dynamicBlockBaseDensity_add_maxIncrement]
  simpa only [dynamicThresholdProfile] using
    c.thresholdProfile_le_globalBudget
      (dynamicBlockBaseDensity pc eta) (dynamicBlockIncrement d eta) (pc + eta)
      hbase hdelta hmax hbudget e

/-- Source-valid region data: it contains the inlet seed box and avoids the chosen seeded target
quadrant together with its exterior vertex boundary. -/
def IsAdmissible (c : RestartRevealCellIndex d i m n) : Prop :=
  cubicMetricBox d cubicOrigin m ⊆ c.regionVertices ∧
    RegionAvoidsSeededBoundaryQuadrant d i n c.regionVertices

/-- Concrete oriented query carried by a reveal cell. -/
noncomputable def orientedQuery
    (c : RestartRevealCellIndex d i m n)
    (center : Cubic d) (direction : CubicDirection d)
    (base delta : ℝ) (hbase : 0 ≤ base) (hdelta : 0 ≤ delta)
    (hupper : base + (2 * d + 1 : ℕ) * delta ≤ 1) :
    OrientedRestartQuery d where
  center := center
  direction := direction
  region := c.regionVertices
  beta := c.thresholdProfile base delta hbase hdelta hupper

end RestartRevealCellIndex

namespace AdaptiveSiteExploration

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Build one partitioned restart stage from an exact finite reveal algorithm.  The sole
algorithm-specific semantic equation is `hcell`: on fiber `c`, the current exact history is the
independent earlier information intersected with the closed boundary of `query c`. -/
noncomputable def PartitionedOrientedRestartStage.ofFiniteRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → OrientedRestartQuery d)
    (pastSupport : C → Finset (CubicEdge d))
    (past : C → Set (CubicEdge d → ℝ))
    (hpast : ∀ c, (MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c)))
    (hfresh : ∀ c, Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d)))
    (hcell : ∀ c,
      past c ∩ (query c).boundaryHistoryEvent n =
        exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      (1 - epsilon) *
          (couplingMeasure (CubicEdge d)).real
            ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    PartitionedOrientedRestartStage d C m n p delta epsilon where
  cells := Finset.univ
  query := query
  pastSupport := pastSupport
  past := past
  past_measurable := fun c _hc => hpast c
  fresh := fun c _hc => hfresh c
  pairwise_cells := by
    intro c hc c' hc' hcc'
    change Disjoint (past c ∩ (query c).boundaryHistoryEvent n)
      (past c' ∩ (query c').boundaryHistoryEvent n)
    rw [hcell c, hcell c']
    exact pairwiseDisjoint_exactRevealCellEvent Finset.univ history realizedCell
      (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc') hcc'
  restart_gt := fun c _hc => hrestart c

theorem PartitionedOrientedRestartStage.cellUnion_ofFiniteRealization
    {d m n : ℕ} {p : I} {delta epsilon : ℝ}
    (history : Set (CubicEdge d → ℝ))
    (realizedCell : (CubicEdge d → ℝ) → C)
    (query : C → OrientedRestartQuery d)
    (pastSupport : C → Finset (CubicEdge d))
    (past : C → Set (CubicEdge d → ℝ))
    (hpast : ∀ c, (MeasurableSet[coordSigma (CubicEdge d)
      (pastSupport c : Set (CubicEdge d))] (past c)))
    (hfresh : ∀ c, Disjoint (pastSupport c : Set (CubicEdge d))
      ((query c).restartSupport m n : Set (CubicEdge d)))
    (hcell : ∀ c,
      past c ∩ (query c).boundaryHistoryEvent n =
        exactRevealCellEvent history realizedCell c)
    (hrestart : ∀ c,
      (1 - epsilon) *
          (couplingMeasure (CubicEdge d)).real
            ((query c).boundaryHistoryEvent n) <
        (couplingMeasure (CubicEdge d)).real
          ((query c).successEvent m n p delta ∩
            (query c).boundaryHistoryEvent n)) :
    (PartitionedOrientedRestartStage.ofFiniteRealization history realizedCell query
      pastSupport past hpast hfresh hcell hrestart).cellUnion = history := by
  rw [PartitionedOrientedRestartStage.cellUnion]
  change (⋃ c ∈ (Finset.univ : Finset C),
    past c ∩ (query c).boundaryHistoryEvent n) = history
  simp_rw [hcell]
  exact biUnion_univ_exactRevealCellEvent history realizedCell

end AdaptiveSiteExploration

end Percolation
