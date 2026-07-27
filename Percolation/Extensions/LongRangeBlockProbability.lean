import Percolation.Extensions.LongRangeBlocks

/-!
# Probability estimates for hierarchical long-range blocks

This file begins the probabilistic Newman--Schulman induction.  It identifies the exact
level-zero cylinder probability and packages finite child-block independence.  Cross-block
connection estimates are developed in the following layer.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology unitInterval

theorem longRangeEdgeDistance_eq_one_of_mem_blockNearestEdges
    {base arity k : ℕ} {z : ℤ} {e : Sym2 ℤ}
    (he : e ∈ longRangeBlockNearestEdges base arity k z) :
    longRangeEdgeDistance e = 1 := by
  classical
  rw [longRangeBlockNearestEdges, Finset.mem_image] at he
  rcases he with ⟨x, _hx, rfl⟩
  simp [longRangeEdgeDistance_mk]

/-- Exact probability of the all-nearest-open seed cylinder. -/
theorem longRangeMeasure_real_blockNearestOpen
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (base arity k : ℕ) (z : ℤ) :
    (longRangeMeasure (F q)).real
        {ω : LongRangeConfiguration |
          (longRangeBlockNearestEdges base arity k z : Set (Sym2 ℤ)) ⊆ ω} =
      (q : ℝ) ^ (longRangeBlockNearestEdges base arity k z).card := by
  rw [longRangeMeasure_real_superset_finset]
  calc
    (∏ e ∈ longRangeBlockNearestEdges base arity k z,
        (F q (longRangeEdgeDistance e) : ℝ)) =
        ∏ _e ∈ longRangeBlockNearestEdges base arity k z, (q : ℝ) := by
      apply Finset.prod_congr rfl
      intro e he
      rw [longRangeEdgeDistance_eq_one_of_mem_blockNearestEdges he,
        F.nearestNeighbour]
    _ = (q : ℝ) ^ (longRangeBlockNearestEdges base arity k z).card := by simp

/-- Level-zero good-block probability is at least its explicit nearest-neighbour seed
probability. -/
theorem longRangeMeasure_real_geometricBlockGood_zero_ge
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    {base arity quota : ℕ} (hbase : 0 < base) (z : ℤ) :
    (q : ℝ) ^ (longRangeBlockNearestEdges base arity 0 z).card ≤
      (longRangeMeasure (F q)).real
        (longRangeGeometricBlockGoodEvent base arity quota 0 z) := by
  rw [← longRangeMeasure_real_blockNearestOpen F q base arity 0 z]
  exact measureReal_mono
    (nearestOpen_subset_longRangeGeometricBlockGoodEvent hbase z)

/-- At fixed base scale the seed probability tends to one as the nearest-neighbour parameter
tends to one. -/
theorem tendsto_longRange_blockNearestOpen_probability_one
    (base arity k : ℕ) (z : ℤ) :
    Tendsto
      (fun q : I ↦ (q : ℝ) ^ (longRangeBlockNearestEdges base arity k z).card)
      (𝓝 (1 : I)) (𝓝 1) := by
  have hcont : ContinuousAt (fun q : I ↦ (q : ℝ)) (1 : I) :=
    continuous_subtype_val.continuousAt
  simpa using
    (hcont.pow (longRangeBlockNearestEdges base arity k z).card).tendsto

theorem longRangeBlockEdgeSupport_children_disjoint
    {base arity k : ℕ} (hbase : 0 < base) (harity : 0 < arity) (z : ℤ)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint
      (longRangeBlockEdgeSupport base arity k (z * arity + i))
      (longRangeBlockEdgeSupport base arity k (z * arity + j)) := by
  classical
  rw [Finset.disjoint_left]
  intro e hei hej
  rw [longRangeBlockEdgeSupport, Finset.mem_image] at hei hej
  rcases hei with ⟨⟨a, b⟩, hab, rfl⟩
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  rcases hej with ⟨⟨c, d⟩, hcd, heq⟩
  rcases Finset.mem_product.mp hcd with ⟨hc, hd⟩
  simp only at ha hb hc hd heq
  have haedge : a ∈ s(a, b) := by simp
  rw [← heq] at haedge
  have haOther : a ∈
      longRangeBlockVertices base arity k (z * arity + j) := by
    simp only [Sym2.mem_iff] at haedge
    rcases haedge with rfl | rfl
    · exact hc
    · exact hd
  exact Finset.disjoint_left.mp
    (longRangeBlockVertices_children_disjoint hbase harity z hij) ha haOther

/-- Good events in the child blocks are mutually independent because every one is supported on
the unordered pairs internal to its own child interval. -/
theorem iIndepSet_longRangeGeometricBlockGoodEvent_children
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    {base arity quota k : ℕ} (hbase : 0 < base) (harity : 0 < arity) (z : ℤ) :
    iIndepSet
      (fun i : Fin arity ↦
        longRangeGeometricBlockGoodEvent base arity quota k (z * arity + i.val))
      (longRangeMeasure (F q)) := by
  change iIndepSet _ (inhomogeneousSetBernoulli (longRangeEdgeDensity (F q)))
  apply inhomogeneousSetBernoulli_iIndepSet_of_pairwiseDisjoint_dependsOn
    (longRangeEdgeDensity (F q))
    (fun i : Fin arity ↦
      longRangeBlockEdgeSupport base arity k (z * arity + i.val))
  · intro i
    exact dependsOn_longRangeGeometricBlockGoodEvent
      base arity quota k (z * arity + i.val)
  · intro i _hi j _hj hij
    exact longRangeBlockEdgeSupport_children_disjoint hbase harity z
      (fun h ↦ hij (Fin.ext h))

/-! ### A finite independent-failure bound -/

/-- At least `b` of a finite family of events fail. -/
def finiteAtLeastFailuresEvent {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Set Ω) (b : ℕ) : Set Ω := by
  classical
  exact {ω | b ≤ (Finset.univ.filter fun i ↦ ω ∉ A i).card}

theorem finiteAtLeastFailuresEvent_subset_biUnion
    {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Set Ω) (b : ℕ) :
    finiteAtLeastFailuresEvent A b ⊆
      ⋃ J ∈ Finset.univ.powersetCard b, ⋂ i ∈ J, (A i)ᶜ := by
  classical
  intro ω hω
  change b ≤ (Finset.univ.filter fun i ↦ ω ∉ A i).card at hω
  obtain ⟨J, hJsub, hJcard⟩ :=
    (Finset.univ.filter fun i ↦ ω ∉ A i).exists_subset_card_eq hω
  refine Set.mem_iUnion.2 ⟨J, ?_⟩
  refine Set.mem_iUnion.2 ⟨Finset.mem_powersetCard.mpr
    ⟨hJsub.trans (Finset.filter_subset _ _), hJcard⟩, ?_⟩
  refine Set.mem_iInter.2 fun i ↦ Set.mem_iInter.2 fun hi ↦ ?_
  exact (Finset.mem_filter.mp (hJsub hi)).2

/-- If independent events each fail with probability at most `ε`, the probability that at least
`b` fail is at most `2^|ι| ε^b`.  The powerset factor is deliberately coarse; it is the stable
form needed by the block recursion. -/
theorem measureReal_finiteAtLeastFailuresEvent_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hind : iIndepSet A μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : ∀ i, μ.real (A i)ᶜ ≤ ε) (b : ℕ) :
    μ.real (finiteAtLeastFailuresEvent A b) ≤
      (2 : ℝ) ^ Fintype.card ι * ε ^ b := by
  let S : Finset (Finset ι) := Finset.univ.powersetCard b
  let B : Finset ι → Set Ω := fun J ↦ ⋂ i ∈ J, (A i)ᶜ
  calc
    μ.real (finiteAtLeastFailuresEvent A b) ≤ μ.real (⋃ J ∈ S, B J) :=
      measureReal_mono (finiteAtLeastFailuresEvent_subset_biUnion A b)
        (measure_ne_top μ _)
    _ ≤ ∑ J ∈ S, μ.real (B J) := measureReal_biUnion_finset_le S B
    _ ≤ ∑ _J ∈ S, ε ^ b := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJcard : J.card = b := (Finset.mem_powersetCard.mp hJ).2
      have hfactor := (iIndepSet_compl hind).meas_biInter J
      have hfactorReal : μ.real (B J) = ∏ i ∈ J, μ.real (A i)ᶜ := by
        simpa only [B, measureReal_def, ENNReal.toReal_prod] using
          congrArg ENNReal.toReal hfactor
      rw [hfactorReal, ← hJcard]
      calc
        ∏ i ∈ J, μ.real (A i)ᶜ ≤ ∏ _i ∈ J, ε := by
          exact Finset.prod_le_prod (fun i _hi ↦ measureReal_nonneg)
            (fun i _hi ↦ hfail i)
        _ = ε ^ J.card := by simp
    _ = S.card * ε ^ b := by simp
    _ ≤ (2 : ℝ) ^ Fintype.card ι * ε ^ b := by
      have hScard : S.card ≤ 2 ^ Fintype.card ι := by
        calc
          S.card ≤ Finset.univ.powerset.card := Finset.card_le_card (by
            intro J hJ
            exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1)
          _ = 2 ^ Fintype.card ι := by simp
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) (pow_nonneg hε b)

end Percolation
