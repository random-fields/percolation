import Percolation.Extensions.LongRangeBlockInduction

/-!
# Newman--Schulman good-block recursion

This file combines independent child failures, canonical cross-component traces, and the
deterministic parent induction into the quantitative recursion used in Grimmett Theorem 12.8.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology unitInterval

/-- Child-good event at a fixed parent and level. -/
def longRangeChildGoodEvent (base arity quota k : ℕ) (z : ℤ) (i : Fin arity) :
    Set LongRangeConfiguration :=
  longRangeGeometricBlockGoodEvent base arity quota k (z * arity + i.val)

/-- Union of pair failures over all distinct ordered child pairs. -/
def longRangeChildPairUnlinkedUnion
    (base arity quota k : ℕ) (z : ℤ) : Set LongRangeConfiguration :=
  ⋃ i : Fin arity, ⋃ j : Fin arity,
    if i = j then ∅ else
      longRangeSelectedPairUnlinkedEvent
        (longRangeBlockVertices base arity k (z * arity + i.val))
        (longRangeBlockVertices base arity k (z * arity + j.val))
        (longRangeBlockTargetSize base quota k)

/-- A bad parent either has too many bad children or contains two large selected child
components that fail to link. -/
theorem compl_geometricBlockGood_succ_subset
    {base arity quota k : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (hquota : 0 < quota) (hquotaArity : quota ≤ arity) (z : ℤ) :
    (longRangeGeometricBlockGoodEvent base arity quota (k + 1) z)ᶜ ⊆
      finiteAtLeastFailuresEvent
          (longRangeChildGoodEvent base arity quota k z)
          (arity - quota + 1) ∪
        longRangeChildPairUnlinkedUnion base arity quota k z := by
  classical
  intro ω hparentBad
  by_cases hmany : ω ∈ finiteAtLeastFailuresEvent
      (longRangeChildGoodEvent base arity quota k z) (arity - quota + 1)
  · exact Or.inl hmany
  · apply Or.inr
    by_contra hpairs
    let J : Finset (Fin arity) := Finset.univ.filter fun i ↦
      ω ∈ longRangeChildGoodEvent base arity quota k z i
    have hcount : quota ≤ J.card := by
      change ¬arity - quota + 1 ≤
        (Finset.univ.filter fun i : Fin arity ↦
          ω ∉ longRangeChildGoodEvent base arity quota k z i).card at hmany
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin arity)))
        (fun i ↦ ω ∈ longRangeChildGoodEvent base arity quota k z i)
      have hpartition' : J.card +
        (Finset.univ.filter fun i : Fin arity ↦
          ω ∉ longRangeChildGoodEvent base arity quota k z i).card = arity := by
        simpa [J] using hpartition
      omega
    have hgood : ∀ i ∈ J, ω ∈ longRangeGeometricBlockGoodEvent
        base arity quota k (z * arity + i.val) := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hlink : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → longRangeSetsLinked ω
        (longRangeComponentVertexFinset (longRangeSelectedComponent ω
          (longRangeBlockVertices base arity k (z * arity + i.val))
          (longRangeBlockTargetSize base quota k)))
        (longRangeComponentVertexFinset (longRangeSelectedComponent ω
          (longRangeBlockVertices base arity k (z * arity + j.val))
          (longRangeBlockTargetSize base quota k))) := by
      intro i hi j hj hij
      by_contra hunlinked
      apply hpairs
      rw [longRangeChildPairUnlinkedUnion]
      refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
      rw [if_neg hij]
      refine ⟨longRangeSelectedComponent_spec (hgood i hi),
        longRangeSelectedComponent_spec (hgood j hj), hunlinked⟩
    apply hparentBad
    exact mem_longRangeGeometricBlockGoodEvent_succ_of_children
      hbase harity hquota z ω J hcount hgood hlink

/-- Union-bound estimate for all distinct selected-child pair failures. -/
theorem longRangeMeasure_real_childPairUnlinkedUnion_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {base arity quota k : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (z : ℤ) :
    (longRangeMeasure (F q)).real
        (longRangeChildPairUnlinkedUnion base arity quota k z) ≤
      (arity : ℝ) ^ 2 *
        Real.exp (-β /
          (longRangeBlockLength base arity (k + 1) : ℝ) ^ α) ^
            (longRangeBlockTargetSize base quota k ^ 2) := by
  let r := Real.exp (-β /
    (longRangeBlockLength base arity (k + 1) : ℝ) ^ α) ^
      (longRangeBlockTargetSize base quota k ^ 2)
  rw [longRangeChildPairUnlinkedUnion]
  calc
    (longRangeMeasure (F q)).real
        (⋃ i : Fin arity, ⋃ j : Fin arity,
          if i = j then ∅ else longRangeSelectedPairUnlinkedEvent
            (longRangeBlockVertices base arity k (z * arity + i.val))
            (longRangeBlockVertices base arity k (z * arity + j.val))
            (longRangeBlockTargetSize base quota k)) ≤
        ∑ i : Fin arity, (longRangeMeasure (F q)).real
          (⋃ j : Fin arity, if i = j then ∅ else
            longRangeSelectedPairUnlinkedEvent
              (longRangeBlockVertices base arity k (z * arity + i.val))
              (longRangeBlockVertices base arity k (z * arity + j.val))
              (longRangeBlockTargetSize base quota k)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin arity, ∑ _j : Fin arity, r := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        (longRangeMeasure (F q)).real
            (⋃ j : Fin arity, if i = j then ∅ else
              longRangeSelectedPairUnlinkedEvent
                (longRangeBlockVertices base arity k (z * arity + i.val))
                (longRangeBlockVertices base arity k (z * arity + j.val))
                (longRangeBlockTargetSize base quota k)) ≤
            ∑ j : Fin arity, (longRangeMeasure (F q)).real
              (if i = j then ∅ else longRangeSelectedPairUnlinkedEvent
                (longRangeBlockVertices base arity k (z * arity + i.val))
                (longRangeBlockVertices base arity k (z * arity + j.val))
                (longRangeBlockTargetSize base quota k)) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ _j : Fin arity, r := by
          apply Finset.sum_le_sum
          intro j _hj
          by_cases hij : i = j
          · simp [hij, r, (Real.exp_pos _).le]
          · rw [if_neg hij]
            simpa [r, pow_two] using
              longRangeMeasure_real_selectedPairUnlinked_le
                F q hβ hα hq hbase harity z hij
    _ = (arity : ℝ) ^ 2 * r := by
      simp [pow_two]
      ring
    _ = (arity : ℝ) ^ 2 *
        Real.exp (-β /
          (longRangeBlockLength base arity (k + 1) : ℝ) ^ α) ^
            (longRangeBlockTargetSize base quota k ^ 2) := rfl

/-- Quantitative one-step good-block recursion. -/
theorem longRangeMeasure_real_geometricBlockGood_succ_compl_le
    {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I)
    (hβ : 0 < β) (hα : 0 < α)
    (hq : longRangePowerLawTailProbability β α 1 ≤ q)
    {base arity quota k : ℕ} (hbase : 0 < base) (harity : 0 < arity)
    (hquota : 0 < quota) (hquotaArity : quota ≤ arity)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hchild : ∀ w : ℤ, (longRangeMeasure (F q)).real
      (longRangeGeometricBlockGoodEvent base arity quota k w)ᶜ ≤ ε)
    (z : ℤ) :
    (longRangeMeasure (F q)).real
        (longRangeGeometricBlockGoodEvent base arity quota (k + 1) z)ᶜ ≤
      (2 : ℝ) ^ arity * ε ^ (arity - quota + 1) +
        (arity : ℝ) ^ 2 *
          Real.exp (-β /
            (longRangeBlockLength base arity (k + 1) : ℝ) ^ α) ^
              (longRangeBlockTargetSize base quota k ^ 2) := by
  let A := longRangeChildGoodEvent base arity quota k z
  have hind : iIndepSet A (longRangeMeasure (F q)) := by
    simpa [A, longRangeChildGoodEvent] using
      iIndepSet_longRangeGeometricBlockGoodEvent_children
        F q hbase harity z (quota := quota) (k := k)
  have hfail : ∀ i, (longRangeMeasure (F q)).real (A i)ᶜ ≤ ε := by
    intro i
    exact hchild (z * arity + i.val)
  calc
    (longRangeMeasure (F q)).real
        (longRangeGeometricBlockGoodEvent base arity quota (k + 1) z)ᶜ ≤
        (longRangeMeasure (F q)).real
          (finiteAtLeastFailuresEvent A (arity - quota + 1) ∪
            longRangeChildPairUnlinkedUnion base arity quota k z) :=
      measureReal_mono
        (compl_geometricBlockGood_succ_subset hbase harity hquota hquotaArity z)
        (measure_ne_top _ _)
    _ ≤ (longRangeMeasure (F q)).real
          (finiteAtLeastFailuresEvent A (arity - quota + 1)) +
        (longRangeMeasure (F q)).real
          (longRangeChildPairUnlinkedUnion base arity quota k z) :=
      measureReal_union_le _ _
    _ ≤ (2 : ℝ) ^ arity * ε ^ (arity - quota + 1) +
        (arity : ℝ) ^ 2 *
          Real.exp (-β /
            (longRangeBlockLength base arity (k + 1) : ℝ) ^ α) ^
              (longRangeBlockTargetSize base quota k ^ 2) := by
      gcongr
      · simpa using measureReal_finiteAtLeastFailuresEvent_le
          (longRangeMeasure (F q)) A (fun i ↦
            measurableSet_longRangeGeometricBlockGoodEvent base arity quota k
              (z * arity + i.val)) hind hε hfail (arity - quota + 1)
      · exact longRangeMeasure_real_childPairUnlinkedUnion_le
          F q hβ hα hq hbase harity z

end Percolation
