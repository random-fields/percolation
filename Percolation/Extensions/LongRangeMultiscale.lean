import Percolation.Extensions.LongRangeBlockRecursion

/-!
# Variable-scale long-range renormalization

Fixed arity loses a fixed fraction of vertices at every level.  Newman--Schulman's argument
uses varying scales so that the retained fractions have a positive product.  This file packages
the already-proved one-step geometry for an arbitrary interval length, child quota, and component
target, allowing successive steps to use different arities.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology unitInterval

/-- An aligned integer interval of literal length `L`. -/
noncomputable def longRangeIntervalBlock (L : ℕ) (z : ℤ) : Finset ℤ :=
  longRangeBlockVertices L 1 0 z

@[simp]
theorem longRangeIntervalBlock_card (L : ℕ) (z : ℤ) :
    (longRangeIntervalBlock L z).card = L := by
  simp [longRangeIntervalBlock, longRangeBlockVertices_card, longRangeBlockLength]

theorem longRangeIntervalBlock_eq_blockVertices_zero (L a : ℕ) (z : ℤ) :
    longRangeIntervalBlock L z = longRangeBlockVertices L a 0 z := by
  ext x
  simp [longRangeIntervalBlock, mem_longRangeBlockVertices_iff, longRangeBlockLength]

theorem longRangeIntervalBlock_mul_eq_blockVertices_one (L a : ℕ) (z : ℤ) :
    longRangeIntervalBlock (L * a) z = longRangeBlockVertices L a 1 z := by
  ext x
  simp [longRangeIntervalBlock, mem_longRangeBlockVertices_iff, longRangeBlockLength]

/-- A block contains an internal open component of at least `m` vertices. -/
def longRangeIntervalLargeComponentEvent (L m : ℕ) (z : ℤ) :
    Set LongRangeConfiguration :=
  {ω | ∃ x : longRangeIntervalBlock L z,
    m ≤ (longRangeComponentInFinset ω (longRangeIntervalBlock L z) x).card}

theorem isIncreasingEvent_longRangeIntervalLargeComponentEvent (L m : ℕ) (z : ℤ) :
    IsIncreasingEvent (longRangeIntervalLargeComponentEvent L m z) := by
  intro ω η hωη
  rintro ⟨x, hx⟩
  exact ⟨x, hx.trans (card_longRangeComponentInFinset_mono hωη _ x)⟩

theorem longRangeIntervalLargeComponentEvent_eq_geometric
    (L a quota : ℕ) (z : ℤ) :
    longRangeIntervalLargeComponentEvent L L z =
      longRangeGeometricBlockGoodEvent L a quota 0 z := by
  ext ω
  simp only [longRangeIntervalLargeComponentEvent,
    longRangeGeometricBlockGoodEvent, Set.mem_setOf_eq,
    longRangeBlockTargetSize_zero]
  rw [longRangeIntervalBlock_eq_blockVertices_zero L a z]

/-- Literal internal-pair support for a variable-scale interval event. -/
noncomputable def longRangeAlignedIntervalEdgeSupport (L : ℕ) (z : ℤ) : Finset (Sym2 ℤ) :=
  ((longRangeIntervalBlock L z) ×ˢ longRangeIntervalBlock L z).image
    fun xy ↦ s(xy.1, xy.2)

theorem dependsOn_longRangeIntervalLargeComponentEvent (L m : ℕ) (z : ℤ) :
    DependsOn (longRangeAlignedIntervalEdgeSupport L z)
      (longRangeIntervalLargeComponentEvent L m z) := by
  classical
  intro ω η htrace
  let B := longRangeIntervalBlock L z
  have hgraph : (longRangeOpenGraph ω).induce (B : Set ℤ) =
      (longRangeOpenGraph η).induce (B : Set ℤ) := by
    ext x y
    change (longRangeOpenGraph ω).Adj x.val y.val ↔
      (longRangeOpenGraph η).Adj x.val y.val
    rw [longRangeOpenGraph_adj, longRangeOpenGraph_adj]
    apply and_congr
    · exact htrace s(x.val, y.val) (by
        rw [longRangeAlignedIntervalEdgeSupport, Finset.mem_image]
        exact ⟨(x.val, y.val), Finset.mem_product.mpr
          ⟨x.property, y.property⟩, rfl⟩)
    · rfl
  change (∃ x : B, m ≤ (longRangeComponentInFinset ω B x).card) ↔
    ∃ x : B, m ≤ (longRangeComponentInFinset η B x).card
  have hcomp (x : B) : longRangeComponentInFinset ω B x =
      longRangeComponentInFinset η B x := by
    ext y
    rw [mem_longRangeComponentInFinset_iff, mem_longRangeComponentInFinset_iff]
    simpa only [hgraph]
  simp_rw [hcomp]

theorem measurableSet_longRangeIntervalLargeComponentEvent (L m : ℕ) (z : ℤ) :
    MeasurableSet (longRangeIntervalLargeComponentEvent L m z) :=
  (dependsOn_longRangeIntervalLargeComponentEvent L m z).measurableSet

/-- All-nearest-open seed cylinder forces an `L`-vertex component. -/
theorem nearestOpen_subset_longRangeIntervalLargeComponentEvent
    {L m : ℕ} (hL : 0 < L) (hmL : m ≤ L) (z : ℤ) :
    {ω : LongRangeConfiguration |
      (longRangeBlockNearestEdges L 1 0 z : Set (Sym2 ℤ)) ⊆ ω} ⊆
      longRangeIntervalLargeComponentEvent L m z := by
  intro ω hω
  have hgoodGeom := nearestOpen_subset_longRangeGeometricBlockGoodEvent
    (arity := 1) (quota := 1) hL z hω
  have hgood : ω ∈ longRangeIntervalLargeComponentEvent L L z := by
    rw [longRangeIntervalLargeComponentEvent_eq_geometric L 1 1 z]
    exact hgoodGeom
  rcases hgood with ⟨x, hx⟩
  exact ⟨x, hmL.trans hx⟩

/-- Variable-scale selected component. -/
noncomputable def longRangeIntervalSelectedComponent
    (ω : LongRangeConfiguration) (L m : ℕ) (z : ℤ) :
    Finset (longRangeIntervalBlock L z) :=
  longRangeSelectedComponent ω (longRangeIntervalBlock L z) m

/-- Children of a variable-scale parent. -/
def longRangeMultiscaleChildEvent (L a m : ℕ) (z : ℤ) (i : Fin a) :
    Set LongRangeConfiguration :=
  longRangeIntervalLargeComponentEvent L m (z * a + i.val)

theorem iIndepSet_longRangeMultiscaleChildEvent
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    {L a m : ℕ} (hL : 0 < L) (ha : 0 < a) (z : ℤ) :
    iIndepSet (longRangeMultiscaleChildEvent L a m z)
      (longRangeMeasure (F q)) := by
  have heqSupport (i : Fin a) :
      longRangeAlignedIntervalEdgeSupport L (z * a + i.val) =
        longRangeBlockEdgeSupport L a 0 (z * a + i.val) := by
    simp only [longRangeAlignedIntervalEdgeSupport, longRangeBlockEdgeSupport,
      longRangeIntervalBlock_eq_blockVertices_zero L a]
  change iIndepSet _ (inhomogeneousSetBernoulli (longRangeEdgeDensity (F q)))
  apply inhomogeneousSetBernoulli_iIndepSet_of_pairwiseDisjoint_dependsOn
    (longRangeEdgeDensity (F q))
    (fun i : Fin a ↦ longRangeAlignedIntervalEdgeSupport L (z * a + i.val))
  · intro i
    exact dependsOn_longRangeIntervalLargeComponentEvent L m (z * a + i.val)
  · intro i _hi j _hj hij
    change Disjoint (longRangeAlignedIntervalEdgeSupport L (z * a + i.val))
      (longRangeAlignedIntervalEdgeSupport L (z * a + j.val))
    rw [heqSupport i, heqSupport j]
    exact longRangeBlockEdgeSupport_children_disjoint hL ha z
      (fun h ↦ hij (Fin.ext h))

/-- Pair-failure union at one variable-scale step. -/
def longRangeMultiscalePairFailureUnion (L a m : ℕ) (z : ℤ) :
    Set LongRangeConfiguration :=
  ⋃ i : Fin a, ⋃ j : Fin a, if i = j then ∅ else
    longRangeSelectedPairUnlinkedEvent
      (longRangeIntervalBlock L (z * a + i.val))
      (longRangeIntervalBlock L (z * a + j.val)) m

/-- Deterministic variable-scale parent implication. -/
theorem mem_longRangeIntervalLargeComponentEvent_mul_of_children
    {L a b m : ℕ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (z : ℤ) (ω : LongRangeConfiguration) (J : Finset (Fin a))
    (hJcard : b ≤ J.card)
    (hgood : ∀ i ∈ J, ω ∈ longRangeIntervalLargeComponentEvent L m
      (z * a + i.val))
    (hlink : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → longRangeSetsLinked ω
      (longRangeComponentVertexFinset (longRangeIntervalSelectedComponent ω L m
        (z * a + i.val)))
      (longRangeComponentVertexFinset (longRangeIntervalSelectedComponent ω L m
        (z * a + j.val)))) :
    ω ∈ longRangeIntervalLargeComponentEvent (L * a) (b * m) z := by
  have hlarge : ∀ i ∈ J, m ≤ (longRangeSelectedComponent ω
      (longRangeBlockVertices L a 0 (z * a + i.val)) m).card := by
    intro i hi
    have hg := hgood i hi
    have hs := longRangeSelectedComponent_spec hg
    simpa only [longRangeIntervalBlock_eq_blockVertices_zero L a] using hs
  obtain ⟨x, hx⟩ := exists_parent_component_card_ge_of_selectedChildren
    hL ha hb hm z ω J hJcard hlarge (by
      simpa [longRangeIntervalSelectedComponent,
        longRangeIntervalBlock_eq_blockVertices_zero L a] using hlink)
  change ∃ y : longRangeIntervalBlock (L * a) z,
    b * m ≤ (longRangeComponentInFinset ω (longRangeIntervalBlock (L * a) z) y).card
  rw [longRangeIntervalBlock_mul_eq_blockVertices_one L a z]
  exact ⟨x, by simpa using hx⟩

/-- Failure of one variable-scale parent is covered by the child-count and pair-link failures. -/
theorem compl_intervalLargeComponent_mul_subset
    {L a b m : ℕ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hba : b ≤ a) (z : ℤ) :
    (longRangeIntervalLargeComponentEvent (L * a) (b * m) z)ᶜ ⊆
      finiteAtLeastFailuresEvent (longRangeMultiscaleChildEvent L a m z)
          (a - b + 1) ∪
        longRangeMultiscalePairFailureUnion L a m z := by
  classical
  intro ω hparentBad
  by_cases hmany : ω ∈ finiteAtLeastFailuresEvent
      (longRangeMultiscaleChildEvent L a m z) (a - b + 1)
  · exact Or.inl hmany
  · apply Or.inr
    by_contra hpairs
    let J : Finset (Fin a) := Finset.univ.filter fun i ↦
      ω ∈ longRangeMultiscaleChildEvent L a m z i
    have hcount : b ≤ J.card := by
      change ¬a - b + 1 ≤ (Finset.univ.filter fun i : Fin a ↦
        ω ∉ longRangeMultiscaleChildEvent L a m z i).card at hmany
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin a)))
        (fun i ↦ ω ∈ longRangeMultiscaleChildEvent L a m z i)
      have hpartition' : J.card + (Finset.univ.filter fun i : Fin a ↦
          ω ∉ longRangeMultiscaleChildEvent L a m z i).card = a := by
        simpa [J] using hpartition
      omega
    have hgood : ∀ i ∈ J, ω ∈ longRangeIntervalLargeComponentEvent L m
        (z * a + i.val) := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hlink : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → longRangeSetsLinked ω
        (longRangeComponentVertexFinset (longRangeIntervalSelectedComponent ω L m
          (z * a + i.val)))
        (longRangeComponentVertexFinset (longRangeIntervalSelectedComponent ω L m
          (z * a + j.val))) := by
      intro i hi j hj hij
      by_contra hunlinked
      apply hpairs
      rw [longRangeMultiscalePairFailureUnion]
      refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
      rw [if_neg hij]
      exact ⟨longRangeSelectedComponent_spec (hgood i hi),
        longRangeSelectedComponent_spec (hgood j hj), hunlinked⟩
    apply hparentBad
    exact mem_longRangeIntervalLargeComponentEvent_mul_of_children
      hL ha hb hm z ω J hcount hgood hlink

/-- Variable-scale pair-failure union estimate. -/
theorem longRangeMeasure_real_multiscalePairFailureUnion_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {L a m : ℕ} (hL : 0 < L) (ha : 0 < a) (z : ℤ) :
    (longRangeMeasure (F q)).real
        (longRangeMultiscalePairFailureUnion L a m z) ≤
      (a : ℝ) ^ 2 * Real.exp (-β / ((L * a : ℕ) : ℝ) ^ α) ^ (m ^ 2) := by
  let r := Real.exp (-β / ((L * a : ℕ) : ℝ) ^ α) ^ (m ^ 2)
  rw [longRangeMultiscalePairFailureUnion]
  calc
    (longRangeMeasure (F q)).real
        (⋃ i : Fin a, ⋃ j : Fin a, if i = j then ∅ else
          longRangeSelectedPairUnlinkedEvent
            (longRangeIntervalBlock L (z * a + i.val))
            (longRangeIntervalBlock L (z * a + j.val)) m) ≤
        ∑ i : Fin a, (longRangeMeasure (F q)).real
          (⋃ j : Fin a, if i = j then ∅ else
            longRangeSelectedPairUnlinkedEvent
              (longRangeIntervalBlock L (z * a + i.val))
              (longRangeIntervalBlock L (z * a + j.val)) m) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, r := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        (longRangeMeasure (F q)).real
            (⋃ j : Fin a, if i = j then ∅ else
              longRangeSelectedPairUnlinkedEvent
                (longRangeIntervalBlock L (z * a + i.val))
                (longRangeIntervalBlock L (z * a + j.val)) m) ≤
            ∑ j : Fin a, (longRangeMeasure (F q)).real
              (if i = j then ∅ else longRangeSelectedPairUnlinkedEvent
                (longRangeIntervalBlock L (z * a + i.val))
                (longRangeIntervalBlock L (z * a + j.val)) m) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ _j : Fin a, r := by
          apply Finset.sum_le_sum
          intro j _hj
          by_cases hij : i = j
          · simp [hij, r, (Real.exp_pos _).le]
          · rw [if_neg hij]
            simpa [r, longRangeIntervalBlock_eq_blockVertices_zero L a,
              longRangeBlockLength, pow_two] using
              longRangeMeasure_real_selectedPairUnlinked_le
                F q hβ hα hq hL ha z hij (k := 0) (m := m)
    _ = (a : ℝ) ^ 2 * r := by
      simp [pow_two]
      ring
    _ = (a : ℝ) ^ 2 *
        Real.exp (-β / ((L * a : ℕ) : ℝ) ^ α) ^ (m ^ 2) := rfl

/-- Complete variable-scale one-step recursion. -/
theorem longRangeMeasure_real_intervalLargeComponent_mul_compl_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {L a b m : ℕ} (hL : 0 < L) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hba : b ≤ a) {ε : ℝ} (hε : 0 ≤ ε)
    (hchild : ∀ w : ℤ, (longRangeMeasure (F q)).real
      (longRangeIntervalLargeComponentEvent L m w)ᶜ ≤ ε)
    (z : ℤ) :
    (longRangeMeasure (F q)).real
        (longRangeIntervalLargeComponentEvent (L * a) (b * m) z)ᶜ ≤
      (2 : ℝ) ^ a * ε ^ (a - b + 1) +
        (a : ℝ) ^ 2 * Real.exp (-β / ((L * a : ℕ) : ℝ) ^ α) ^ (m ^ 2) := by
  let A := longRangeMultiscaleChildEvent L a m z
  have hind := iIndepSet_longRangeMultiscaleChildEvent F q hL ha z (m := m)
  have hfail : ∀ i, (longRangeMeasure (F q)).real (A i)ᶜ ≤ ε := by
    intro i
    exact hchild (z * a + i.val)
  calc
    (longRangeMeasure (F q)).real
        (longRangeIntervalLargeComponentEvent (L * a) (b * m) z)ᶜ ≤
        (longRangeMeasure (F q)).real
          (finiteAtLeastFailuresEvent A (a - b + 1) ∪
            longRangeMultiscalePairFailureUnion L a m z) :=
      measureReal_mono (compl_intervalLargeComponent_mul_subset
        hL ha hb hm hba z) (measure_ne_top _ _)
    _ ≤ (longRangeMeasure (F q)).real
          (finiteAtLeastFailuresEvent A (a - b + 1)) +
        (longRangeMeasure (F q)).real
          (longRangeMultiscalePairFailureUnion L a m z) :=
      measureReal_union_le _ _
    _ ≤ (2 : ℝ) ^ a * ε ^ (a - b + 1) +
        (a : ℝ) ^ 2 * Real.exp (-β / ((L * a : ℕ) : ℝ) ^ α) ^ (m ^ 2) := by
      gcongr
      · simpa using measureReal_finiteAtLeastFailuresEvent_le
          (longRangeMeasure (F q)) A
          (fun i ↦ measurableSet_longRangeIntervalLargeComponentEvent L m
            (z * a + i.val)) hind hε hfail (a - b + 1)
      · exact longRangeMeasure_real_multiscalePairFailureUnion_le
          F q hβ hα hq hL ha z

end Percolation
