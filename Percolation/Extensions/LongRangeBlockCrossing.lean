import Percolation.Extensions.LongRangeBlockProbability
import Mathlib.Data.Int.Lemmas

/-!
# Cross-bond estimates for long-range blocks

This file supplies the quantitative bond estimate used in the Newman--Schulman recursion.
The estimate is first proved for two fixed finite vertex sets; later files apply it after
partitioning the internal block traces according to their canonical selected components.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology unitInterval

/-- All unordered bonds with one endpoint in `C` and the other in `D`. -/
noncomputable def longRangeCrossEdges (C D : Finset ℤ) : Finset (Sym2 ℤ) :=
  (C ×ˢ D).image fun xy ↦ s(xy.1, xy.2)

theorem mem_longRangeCrossEdges_iff {C D : Finset ℤ} {e : Sym2 ℤ} :
    e ∈ longRangeCrossEdges C D ↔
      ∃ x ∈ C, ∃ y ∈ D, e = s(x, y) := by
  classical
  rw [longRangeCrossEdges, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    exact ⟨x, (Finset.mem_product.mp hxy).1, y,
      (Finset.mem_product.mp hxy).2, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

theorem not_longRangeSetsLinked_iff_disjoint_crossEdges
    (ω : LongRangeConfiguration) (C D : Finset ℤ) :
    ¬longRangeSetsLinked ω C D ↔
      Disjoint (longRangeCrossEdges C D : Set (Sym2 ℤ)) ω := by
  rw [Set.disjoint_left]
  constructor
  · intro h e he hω
    change e ∈ longRangeCrossEdges C D at he
    rw [mem_longRangeCrossEdges_iff] at he
    rcases he with ⟨x, hx, y, hy, rfl⟩
    exact h ⟨x, hx, y, hy, hω⟩
  · intro h ⟨x, hx, y, hy, hω⟩
    exact h (mem_longRangeCrossEdges_iff.mpr ⟨x, hx, y, hy, rfl⟩) hω

/-- Across disjoint vertex sets, the unordered-pair map is injective. -/
theorem card_longRangeCrossEdges {C D : Finset ℤ} (hCD : Disjoint C D) :
    (longRangeCrossEdges C D).card = C.card * D.card := by
  classical
  rw [longRangeCrossEdges, Finset.card_image_iff.mpr]
  · simp
  · rintro ⟨x, y⟩ hxy ⟨u, v⟩ huv heq
    rcases Finset.mem_product.mp hxy with ⟨hxC, hyD⟩
    rcases Finset.mem_product.mp huv with ⟨huC, hvD⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨hxv, hyu⟩
    · rfl
    · exact (Finset.disjoint_left.mp hCD hxC (hxv ▸ hvD)).elim

/-- Forget the subtype carried by a component finset. -/
def longRangeComponentVertexFinset {B : Finset ℤ} (C : Finset B) : Finset ℤ :=
  C.map (Function.Embedding.subtype fun x : ℤ ↦ x ∈ B)

@[simp]
theorem card_longRangeComponentVertexFinset {B : Finset ℤ} (C : Finset B) :
    (longRangeComponentVertexFinset C).card = C.card := by
  simp [longRangeComponentVertexFinset]

theorem longRangeComponentVertexFinset_subset {B : Finset ℤ} (C : Finset B) :
    longRangeComponentVertexFinset C ⊆ B := by
  intro x hx
  rw [longRangeComponentVertexFinset, Finset.mem_map] at hx
  rcases hx with ⟨y, _hy, rfl⟩
  exact y.property

/-- Event that the canonical component selector returns exactly `C`. -/
def longRangeSelectedComponentEqEvent (B : Finset ℤ) (m : ℕ) (C : Finset B) :
    Set LongRangeConfiguration :=
  {ω | longRangeSelectedComponent ω B m = C}

theorem dependsOn_longRangeSelectedComponentEqEvent
    (base arity k : ℕ) (z : ℤ) (m : ℕ)
    (C : Finset (longRangeBlockVertices base arity k z)) :
    DependsOn (longRangeBlockEdgeSupport base arity k z)
      (longRangeSelectedComponentEqEvent
        (longRangeBlockVertices base arity k z) m C) := by
  intro ω η htrace
  change (longRangeSelectedComponent ω _ m = C) ↔
    (longRangeSelectedComponent η _ m = C)
  have heq := dependsOnFun_longRangeSelectedComponent base arity k z m htrace
  change longRangeSelectedComponent ω _ m =
    longRangeSelectedComponent η _ m at heq
  constructor
  · intro h
    exact heq.symm.trans h
  · intro h
    exact heq.trans h

theorem measurableSet_longRangeSelectedComponentEqEvent
    (base arity k : ℕ) (z : ℤ) (m : ℕ)
    (C : Finset (longRangeBlockVertices base arity k z)) :
    MeasurableSet (longRangeSelectedComponentEqEvent
      (longRangeBlockVertices base arity k z) m C) :=
  (dependsOn_longRangeSelectedComponentEqEvent base arity k z m C).measurableSet

theorem longRangeSelectedComponent_subset_attach
    (ω : LongRangeConfiguration) (B : Finset ℤ) (m : ℕ) :
    longRangeSelectedComponent ω B m ⊆ B.attach := by
  intro x hx
  exact Finset.mem_attach B x

theorem iUnion_selectedComponentEqEvent (B : Finset ℤ) (m : ℕ) :
    (⋃ C ∈ B.attach.powerset,
      longRangeSelectedComponentEqEvent B m C) = Set.univ := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  let C := longRangeSelectedComponent ω B m
  exact ⟨C, Finset.mem_powerset.mpr
    (longRangeSelectedComponent_subset_attach ω B m), rfl⟩

theorem pairwiseDisjoint_selectedComponentEqEvent (B : Finset ℤ) (m : ℕ) :
    (B.attach.powerset : Set (Finset B)).PairwiseDisjoint
      (longRangeSelectedComponentEqEvent B m) := by
  intro C _hC D _hD hCD
  change Disjoint (longRangeSelectedComponentEqEvent B m C)
    (longRangeSelectedComponentEqEvent B m D)
  rw [Set.disjoint_left]
  intro ω hωC hωD
  exact hCD (hωC.symm.trans hωD)

theorem sum_measureReal_selectedComponentEqEvent
    (μ : Measure LongRangeConfiguration) [IsProbabilityMeasure μ]
    (B : Finset ℤ) (m : ℕ)
    (hmeas : ∀ C ∈ B.attach.powerset,
      MeasurableSet (longRangeSelectedComponentEqEvent B m C)) :
    ∑ C ∈ B.attach.powerset,
        μ.real (longRangeSelectedComponentEqEvent B m C) = 1 := by
  have hmeasure := measure_biUnion_finset (μ := μ)
    (pairwiseDisjoint_selectedComponentEqEvent B m) hmeas
  rw [iUnion_selectedComponentEqEvent B m, measure_univ] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_sum (fun C _hC ↦ measure_ne_top μ _)] at hreal
  simpa [measureReal_def] using hreal.symm

/-- A fixed finite no-link event uses exactly its cross-edge coordinates. -/
theorem dependsOn_not_longRangeSetsLinked (C D : Finset ℤ) :
    DependsOn (longRangeCrossEdges C D)
      {ω : LongRangeConfiguration | ¬longRangeSetsLinked ω C D} := by
  intro ω η htrace
  constructor
  · intro hω hη
    apply hω
    rcases hη with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, (htrace s(x, y)
      (mem_longRangeCrossEdges_iff.mpr ⟨x, hx, y, hy, rfl⟩)).mpr hxy⟩
  · intro hη hω
    apply hη
    rcases hω with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, (htrace s(x, y)
      (mem_longRangeCrossEdges_iff.mpr ⟨x, hx, y, hy, rfl⟩)).mp hxy⟩

/-- Cross edges between disjoint blocks do not overlap either block's internal-pair support. -/
theorem longRangeCrossEdges_disjoint_internalSupports
    {A B C D : Finset ℤ} (hAB : Disjoint A B)
    (hC : C ⊆ A) (hD : D ⊆ B) :
    Disjoint (longRangeCrossEdges C D)
      ((((A ×ˢ A).image fun xy ↦ s(xy.1, xy.2)) ∪
        ((B ×ˢ B).image fun xy ↦ s(xy.1, xy.2)))) := by
  classical
  rw [Finset.disjoint_left]
  intro e heCross heInternal
  rw [mem_longRangeCrossEdges_iff] at heCross
  rcases heCross with ⟨x, hxC, y, hyD, rfl⟩
  rw [Finset.mem_union] at heInternal
  rcases heInternal with heA | heB
  · rw [Finset.mem_image] at heA
    rcases heA with ⟨⟨u, v⟩, huv, heq⟩
    rcases Finset.mem_product.mp huv with ⟨huA, hvA⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.disjoint_left.mp hAB hvA (hD hyD)
    · exact Finset.disjoint_left.mp hAB huA (hD hyD)
  · rw [Finset.mem_image] at heB
    rcases heB with ⟨⟨u, v⟩, huv, heq⟩
    rcases Finset.mem_product.mp huv with ⟨huB, hvB⟩
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Finset.disjoint_left.mp hAB (hC hxC) huB
    · exact Finset.disjoint_left.mp hAB (hC hxC) hvB

/-- The complement of a power-law bond probability is bounded by the complement at a common
upper distance.  The nearest-neighbour coordinate is covered by the explicit lower bound on
`q`; all longer coordinates use the exact inverse-power formula. -/
theorem one_sub_powerLawFamily_le_exp_upperDistance
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {n L : ℕ} (hn : 0 < n) (hnL : n ≤ L) :
    1 - (F q n : ℝ) ≤ Real.exp (-β / (L : ℝ) ^ α) := by
  have hL : 0 < L := hn.trans_le hnL
  have hnR : 0 < (n : ℝ) := by positivity
  have hLR : 0 < (L : ℝ) := by positivity
  have hpow : (n : ℝ) ^ α ≤ (L : ℝ) ^ α :=
    Real.rpow_le_rpow hnR.le (by exact_mod_cast hnL) hα.le
  have hdiv : β / (L : ℝ) ^ α ≤ β / (n : ℝ) ^ α := by
    exact div_le_div_of_nonneg_left hβ.le (Real.rpow_pos_of_pos hnR α) hpow
  by_cases hn1 : n = 1
  · subst n
    rw [F.nearestNeighbour]
    calc
      1 - (q : ℝ) ≤ 1 - (longRangePowerLawTailProbability β α 1 : ℝ) := by
        linarith [show (longRangePowerLawTailProbability β α 1 : ℝ) ≤ (q : ℝ) from hq]
      _ = Real.exp (-β) := by
        rw [coe_longRangePowerLawTailProbability (by norm_num), max_eq_left hβ.le]
        norm_num
      _ ≤ Real.exp (-β / (L : ℝ) ^ α) := by
        rw [Real.exp_le_exp]
        have hone : 1 ≤ (L : ℝ) ^ α := by
          simpa using Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num)
            (show (1 : ℝ) ≤ L by exact_mod_cast hL) hα.le
        have : β / (L : ℝ) ^ α ≤ β := by
          simpa using (div_le_iff₀ (Real.rpow_pos_of_pos hLR α)).2
            (by nlinarith [hβ, hone])
        have hneg := neg_le_neg this
        convert hneg using 1 <;> ring
  · have hn2 : 2 ≤ n := by omega
    rw [F.powerLawTail q n hn2,
      coe_longRangePowerLawTailProbability hn.ne', max_eq_left hβ.le]
    have hsimp : 1 - (1 - Real.exp (-β / (n : ℝ) ^ α)) =
        Real.exp (-β / (n : ℝ) ^ α) := by ring
    rw [hsimp, Real.exp_le_exp]
    have hneg := neg_le_neg hdiv
    convert hneg using 1 <;> ring

/-- Every cross edge between two subsets of the same aligned block has distance at most the
block length. -/
theorem longRangeEdgeDistance_le_blockLength_of_mem_crossEdges
    {base arity k : ℕ} {z : ℤ} {C D : Finset ℤ}
    (hC : C ⊆ longRangeBlockVertices base arity k z)
    (hD : D ⊆ longRangeBlockVertices base arity k z)
    {e : Sym2 ℤ} (he : e ∈ longRangeCrossEdges C D) :
    longRangeEdgeDistance e ≤ longRangeBlockLength base arity k := by
  rw [mem_longRangeCrossEdges_iff] at he
  rcases he with ⟨x, hx, y, hy, rfl⟩
  rw [longRangeEdgeDistance_mk]
  have hx' := mem_longRangeBlockVertices_iff.mp (hC hx)
  have hy' := mem_longRangeBlockVertices_iff.mp (hD hy)
  have hbound : -(longRangeBlockLength base arity k : ℤ) < y - x ∧
      y - x < (longRangeBlockLength base arity k : ℤ) := by
    constructor <;> omega
  have habslt : (y - x).natAbs <
      ((longRangeBlockLength base arity k : ℕ) : ℤ).natAbs := by
    rw [Int.natAbs_lt_iff_sq_lt]
    nlinarith [hbound.1, hbound.2]
  simp only [Int.natAbs_natCast] at habslt
  omega

theorem longRangeEdgeDistance_pos_of_mem_crossEdges
    {C D : Finset ℤ} (hCD : Disjoint C D)
    {e : Sym2 ℤ} (he : e ∈ longRangeCrossEdges C D) :
    0 < longRangeEdgeDistance e := by
  rw [mem_longRangeCrossEdges_iff] at he
  rcases he with ⟨x, hx, y, hy, rfl⟩
  rw [longRangeEdgeDistance_mk, Int.natAbs_pos]
  exact sub_ne_zero.mpr fun hxy ↦
    Finset.disjoint_left.mp hCD hx (hxy ▸ hy)

/-- Fixed-set cross-link failure estimate. -/
theorem longRangeMeasure_real_not_setsLinked_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {base arity k : ℕ} {z : ℤ} {C D : Finset ℤ}
    (hbase : 0 < base) (harity : 0 < arity)
    (hC : C ⊆ longRangeBlockVertices base arity k z)
    (hD : D ⊆ longRangeBlockVertices base arity k z)
    (hCD : Disjoint C D) :
    (longRangeMeasure (F q)).real
        {ω | ¬longRangeSetsLinked ω C D} ≤
      Real.exp (-β / (longRangeBlockLength base arity k : ℝ) ^ α) ^
        (C.card * D.card) := by
  have hL : 0 < longRangeBlockLength base arity k := by
    simp [longRangeBlockLength, hbase, harity]
  rw [show {ω | ¬longRangeSetsLinked ω C D} =
      {ω | Disjoint (longRangeCrossEdges C D : Set (Sym2 ℤ)) ω} by
        ext ω
        exact not_longRangeSetsLinked_iff_disjoint_crossEdges ω C D]
  rw [longRangeMeasure_real_disjoint_finset]
  calc
    (∏ e ∈ longRangeCrossEdges C D,
        (1 - (F q (longRangeEdgeDistance e) : ℝ))) ≤
        ∏ _e ∈ longRangeCrossEdges C D,
          Real.exp (-β / (longRangeBlockLength base arity k : ℝ) ^ α) := by
      apply Finset.prod_le_prod
      · intro e _he
        exact sub_nonneg.mpr (unitInterval.le_one (F q (longRangeEdgeDistance e)))
      · intro e he
        apply one_sub_powerLawFamily_le_exp_upperDistance F q hβ hα hq
        · exact longRangeEdgeDistance_pos_of_mem_crossEdges hCD he
        · exact longRangeEdgeDistance_le_blockLength_of_mem_crossEdges hC hD he
    _ = Real.exp (-β / (longRangeBlockLength base arity k : ℝ) ^ α) ^
        (longRangeCrossEdges C D).card := by simp
    _ = Real.exp (-β / (longRangeBlockLength base arity k : ℝ) ^ α) ^
        (C.card * D.card) := by rw [card_longRangeCrossEdges hCD]

/-! ### Canonical-component trace factorization -/

/-- Selected-component events in two distinct child blocks are independent. -/
theorem longRangeMeasure_real_selectedComponentEq_inter
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) {i j : Fin arity} (hij : i ≠ j)
    (C : Finset (longRangeBlockVertices base arity k (z * arity + i.val)))
    (D : Finset (longRangeBlockVertices base arity k (z * arity + j.val))) :
    (longRangeMeasure (F q)).real
        (longRangeSelectedComponentEqEvent _ m C ∩
          longRangeSelectedComponentEqEvent _ m D) =
      (longRangeMeasure (F q)).real
          (longRangeSelectedComponentEqEvent _ m C) *
        (longRangeMeasure (F q)).real
          (longRangeSelectedComponentEqEvent _ m D) := by
  have hind : IndepSet
      (longRangeSelectedComponentEqEvent
        (longRangeBlockVertices base arity k (z * arity + i.val)) m C)
      (longRangeSelectedComponentEqEvent
        (longRangeBlockVertices base arity k (z * arity + j.val)) m D)
      (longRangeMeasure (F q)) := by
    change IndepSet _ _ (inhomogeneousSetBernoulli (longRangeEdgeDensity (F q)))
    exact inhomogeneousSetBernoulli_indepSet_of_dependsOn
      (longRangeEdgeDensity (F q))
      (longRangeBlockEdgeSupport_children_disjoint hbase harity z
        (fun h ↦ hij (Fin.ext h)))
      (dependsOn_longRangeSelectedComponentEqEvent base arity k
        (z * arity + i.val) m C)
      (dependsOn_longRangeSelectedComponentEqEvent base arity k
        (z * arity + j.val) m D)
  have hmeasure := hind.measure_inter_eq_mul
  have hreal := congrArg ENNReal.toReal hmeasure
  simpa [measureReal_def, ENNReal.toReal_mul] using hreal

/-- The pair of canonical selectors is a probability partition, so the probabilities of all
pair traces sum to one. -/
theorem sum_measureReal_selectedComponentEqEvent_product
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) {i j : Fin arity} (hij : i ≠ j) :
    let Bi := longRangeBlockVertices base arity k (z * arity + i.val)
    let Bj := longRangeBlockVertices base arity k (z * arity + j.val)
    ∑ CD ∈ Bi.attach.powerset ×ˢ Bj.attach.powerset,
      (longRangeMeasure (F q)).real
        (longRangeSelectedComponentEqEvent Bi m CD.1 ∩
          longRangeSelectedComponentEqEvent Bj m CD.2) = 1 := by
  dsimp only
  rw [Finset.sum_product]
  simp_rw [longRangeMeasure_real_selectedComponentEq_inter F q hbase harity z hij]
  have hi := sum_measureReal_selectedComponentEqEvent
    (longRangeMeasure (F q))
    (longRangeBlockVertices base arity k (z * arity + i.val)) m
    (fun C _hC ↦ measurableSet_longRangeSelectedComponentEqEvent
      base arity k (z * arity + i.val) m C)
  have hj := sum_measureReal_selectedComponentEqEvent
    (longRangeMeasure (F q))
    (longRangeBlockVertices base arity k (z * arity + j.val)) m
    (fun D _hD ↦ measurableSet_longRangeSelectedComponentEqEvent
      base arity k (z * arity + j.val) m D)
  simp_rw [← Finset.mul_sum]
  rw [hj]
  simpa using hi

/-- For fixed canonical component traces in two children, the probability that both traces
occur and their selected components receive no cross bond has the uniform `m²` bound. -/
theorem longRangeMeasure_real_selectedPairTrace_unlinked_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) {i j : Fin arity} (hij : i ≠ j)
    (C : Finset (longRangeBlockVertices base arity k (z * arity + i.val)))
    (D : Finset (longRangeBlockVertices base arity k (z * arity + j.val)))
    (hCm : m ≤ C.card) (hDm : m ≤ D.card) :
    let Cv := longRangeComponentVertexFinset C
    let Dv := longRangeComponentVertexFinset D
    (longRangeMeasure (F q)).real
        ((longRangeSelectedComponentEqEvent _ m C ∩
            longRangeSelectedComponentEqEvent _ m D) ∩
          {ω | ¬longRangeSetsLinked ω Cv Dv}) ≤
      (longRangeMeasure (F q)).real
          (longRangeSelectedComponentEqEvent _ m C ∩
            longRangeSelectedComponentEqEvent _ m D) *
        Real.exp (-β /
          (longRangeBlockLength base arity (k + 1) : ℝ) ^ α) ^ (m * m) := by
  dsimp only
  let Bi := longRangeBlockVertices base arity k (z * arity + i.val)
  let Bj := longRangeBlockVertices base arity k (z * arity + j.val)
  let Cv := longRangeComponentVertexFinset C
  let Dv := longRangeComponentVertexFinset D
  let H := longRangeSelectedComponentEqEvent Bi m C ∩
    longRangeSelectedComponentEqEvent Bj m D
  let N : Set LongRangeConfiguration := {ω | ¬longRangeSetsLinked ω Cv Dv}
  have hblocks : Disjoint Bi Bj :=
    longRangeBlockVertices_children_disjoint hbase harity z
      (fun h ↦ hij (Fin.ext h))
  have hCvBi : Cv ⊆ Bi := longRangeComponentVertexFinset_subset C
  have hDvBj : Dv ⊆ Bj := longRangeComponentVertexFinset_subset D
  have hCvDv : Disjoint Cv Dv :=
    Disjoint.mono hCvBi hDvBj hblocks
  have hcross : Disjoint
      (longRangeBlockEdgeSupport base arity k (z * arity + i.val) ∪
        longRangeBlockEdgeSupport base arity k (z * arity + j.val))
      (longRangeCrossEdges Cv Dv) := by
    exact (longRangeCrossEdges_disjoint_internalSupports hblocks hCvBi hDvBj).symm
  have hdepH : DependsOn
      (longRangeBlockEdgeSupport base arity k (z * arity + i.val) ∪
        longRangeBlockEdgeSupport base arity k (z * arity + j.val)) H := by
    intro ω η htrace
    apply and_congr
    · exact dependsOn_longRangeSelectedComponentEqEvent base arity k
        (z * arity + i.val) m C
        (fun e he ↦ htrace e (Finset.mem_union_left _ he))
    · exact dependsOn_longRangeSelectedComponentEqEvent base arity k
        (z * arity + j.val) m D
        (fun e he ↦ htrace e (Finset.mem_union_right _ he))
  have hdepN : DependsOn (longRangeCrossEdges Cv Dv) N :=
    dependsOn_not_longRangeSetsLinked Cv Dv
  have hind : IndepSet H N (longRangeMeasure (F q)) := by
    change IndepSet H N (inhomogeneousSetBernoulli (longRangeEdgeDensity (F q)))
    exact inhomogeneousSetBernoulli_indepSet_of_dependsOn
      (longRangeEdgeDensity (F q)) hcross hdepH hdepN
  have hfactorMeasure := hind.measure_inter_eq_mul
  have hfactorReal : (longRangeMeasure (F q)).real (H ∩ N) =
      (longRangeMeasure (F q)).real H * (longRangeMeasure (F q)).real N := by
    have := congrArg ENNReal.toReal hfactorMeasure
    simpa [measureReal_def, ENNReal.toReal_mul] using this
  have hCvParent : Cv ⊆ longRangeBlockVertices base arity (k + 1) z :=
    hCvBi.trans (longRangeBlockVertices_child_subset base arity k z i.isLt)
  have hDvParent : Dv ⊆ longRangeBlockVertices base arity (k + 1) z :=
    hDvBj.trans (longRangeBlockVertices_child_subset base arity k z j.isLt)
  have hN := longRangeMeasure_real_not_setsLinked_le F q hβ hα hq
    hbase harity hCvParent hDvParent hCvDv
  let r := Real.exp (-β /
    (longRangeBlockLength base arity (k + 1) : ℝ) ^ α)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by linarith)
      (Real.rpow_nonneg (by positivity) _)
  have hcards : m * m ≤ Cv.card * Dv.card := by
    rw [show Cv.card = C.card by simp [Cv], show Dv.card = D.card by simp [Dv]]
    exact Nat.mul_le_mul hCm hDm
  have hpows : r ^ (Cv.card * Dv.card) ≤ r ^ (m * m) :=
    pow_le_pow_of_le_one hr0 hr1 hcards
  change (longRangeMeasure (F q)).real (H ∩ N) ≤
    (longRangeMeasure (F q)).real H * r ^ (m * m)
  rw [hfactorReal]
  calc
    (longRangeMeasure (F q)).real H * (longRangeMeasure (F q)).real N ≤
        (longRangeMeasure (F q)).real H * r ^ (Cv.card * Dv.card) := by
      exact mul_le_mul_of_nonneg_left (by simpa [r] using hN) measureReal_nonneg
    _ ≤ (longRangeMeasure (F q)).real H * r ^ (m * m) := by
      exact mul_le_mul_of_nonneg_left hpows measureReal_nonneg

/-- Both canonical child components are large, but no bond joins them. -/
def longRangeSelectedPairUnlinkedEvent (B₁ B₂ : Finset ℤ) (m : ℕ) :
    Set LongRangeConfiguration :=
  {ω | m ≤ (longRangeSelectedComponent ω B₁ m).card ∧
    m ≤ (longRangeSelectedComponent ω B₂ m).card ∧
    ¬longRangeSetsLinked ω
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω B₁ m))
      (longRangeComponentVertexFinset (longRangeSelectedComponent ω B₂ m))}

/-- A selected-pair failure belongs to the finite union indexed by its two canonical component
traces. -/
theorem longRangeSelectedPairUnlinkedEvent_subset_traceUnion
    (B₁ B₂ : Finset ℤ) (m : ℕ) :
    longRangeSelectedPairUnlinkedEvent B₁ B₂ m ⊆
      ⋃ CD ∈ (B₁.attach.powerset.filter fun C ↦ m ≤ C.card) ×ˢ
          (B₂.attach.powerset.filter fun D ↦ m ≤ D.card),
        (longRangeSelectedComponentEqEvent B₁ m CD.1 ∩
            longRangeSelectedComponentEqEvent B₂ m CD.2) ∩
          {ω | ¬longRangeSetsLinked ω
            (longRangeComponentVertexFinset CD.1)
            (longRangeComponentVertexFinset CD.2)} := by
  classical
  intro ω hω
  let C := longRangeSelectedComponent ω B₁ m
  let D := longRangeSelectedComponent ω B₂ m
  have hCpow : C ∈ B₁.attach.powerset :=
    Finset.mem_powerset.mpr (longRangeSelectedComponent_subset_attach ω B₁ m)
  have hDpow : D ∈ B₂.attach.powerset :=
    Finset.mem_powerset.mpr (longRangeSelectedComponent_subset_attach ω B₂ m)
  have hCDmem : (C, D) ∈
      (B₁.attach.powerset.filter fun C ↦ m ≤ C.card) ×ˢ
        (B₂.attach.powerset.filter fun D ↦ m ≤ D.card) := by
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨hCpow, hω.1⟩, hDpow, hω.2.1⟩
  refine Set.mem_iUnion.2 ⟨(C, D), Set.mem_iUnion.2 ⟨hCDmem, ?_⟩⟩
  exact ⟨⟨rfl, rfl⟩, hω.2.2⟩

/-- Uniform cross-link estimate for the two canonical large components in distinct child
blocks.  The trace partition removes any combinatorial factor depending on the block size. -/
theorem longRangeMeasure_real_selectedPairUnlinked_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {base arity k m : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) {i j : Fin arity} (hij : i ≠ j) :
    let Bi := longRangeBlockVertices base arity k (z * arity + i.val)
    let Bj := longRangeBlockVertices base arity k (z * arity + j.val)
    (longRangeMeasure (F q)).real
        (longRangeSelectedPairUnlinkedEvent Bi Bj m) ≤
      Real.exp (-β /
        (longRangeBlockLength base arity (k + 1) : ℝ) ^ α) ^ (m * m) := by
  dsimp only
  let Bi := longRangeBlockVertices base arity k (z * arity + i.val)
  let Bj := longRangeBlockVertices base arity k (z * arity + j.val)
  let Ki := Bi.attach.powerset.filter fun C ↦ m ≤ C.card
  let Kj := Bj.attach.powerset.filter fun D ↦ m ≤ D.card
  let K := Ki ×ˢ Kj
  let T : Finset Bi × Finset Bj → Set LongRangeConfiguration := fun CD ↦
    (longRangeSelectedComponentEqEvent Bi m CD.1 ∩
        longRangeSelectedComponentEqEvent Bj m CD.2) ∩
      {ω | ¬longRangeSetsLinked ω
        (longRangeComponentVertexFinset CD.1)
        (longRangeComponentVertexFinset CD.2)}
  let H : Finset Bi × Finset Bj → Set LongRangeConfiguration := fun CD ↦
    longRangeSelectedComponentEqEvent Bi m CD.1 ∩
      longRangeSelectedComponentEqEvent Bj m CD.2
  let r := Real.exp (-β /
    (longRangeBlockLength base arity (k + 1) : ℝ) ^ α)
  have hsubset : longRangeSelectedPairUnlinkedEvent Bi Bj m ⊆
      ⋃ CD ∈ K, T CD := by
    simpa [Ki, Kj, K, T] using
      longRangeSelectedPairUnlinkedEvent_subset_traceUnion Bi Bj m
  calc
    (longRangeMeasure (F q)).real
        (longRangeSelectedPairUnlinkedEvent Bi Bj m) ≤
        (longRangeMeasure (F q)).real (⋃ CD ∈ K, T CD) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ CD ∈ K, (longRangeMeasure (F q)).real (T CD) :=
      measureReal_biUnion_finset_le K T
    _ ≤ ∑ CD ∈ K,
        (longRangeMeasure (F q)).real (H CD) * r ^ (m * m) := by
      apply Finset.sum_le_sum
      intro CD hCD
      rcases Finset.mem_product.mp hCD with ⟨hCi, hDj⟩
      have hCm : m ≤ CD.1.card := (Finset.mem_filter.mp hCi).2
      have hDm : m ≤ CD.2.card := (Finset.mem_filter.mp hDj).2
      simpa [T, H, r, Bi, Bj] using
        longRangeMeasure_real_selectedPairTrace_unlinked_le F q hβ hα hq
          hbase harity z hij CD.1 CD.2 hCm hDm
    _ = (∑ CD ∈ K, (longRangeMeasure (F q)).real (H CD)) *
        r ^ (m * m) := by rw [Finset.sum_mul]
    _ ≤ 1 * r ^ (m * m) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.exp_pos _).le _)
      have hKsub : K ⊆ Bi.attach.powerset ×ˢ Bj.attach.powerset := by
        intro CD hCD
        rcases Finset.mem_product.mp hCD with ⟨hCi, hDj⟩
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_filter.mp hCi).1, (Finset.mem_filter.mp hDj).1⟩
      calc
        ∑ CD ∈ K, (longRangeMeasure (F q)).real (H CD) ≤
            ∑ CD ∈ Bi.attach.powerset ×ˢ Bj.attach.powerset,
              (longRangeMeasure (F q)).real (H CD) :=
          Finset.sum_le_sum_of_subset_of_nonneg hKsub
            (fun _CD _hfull _hnot ↦ measureReal_nonneg)
        _ = 1 := by
          simpa [H, Bi, Bj] using
            sum_measureReal_selectedComponentEqEvent_product
              F q hbase harity z hij
    _ = r ^ (m * m) := one_mul _

end Percolation
