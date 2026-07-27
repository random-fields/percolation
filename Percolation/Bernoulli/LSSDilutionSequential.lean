import Percolation.Bernoulli.SequentialDominationEvents

/-!
# Sequential lower bounds for a diluted field

This file isolates the final formal implication in equations (7.116)--(7.117).  If, after every
exact diluted prefix, the original next site is open with ratio-free mass at least `a`, and the
fresh retention bit contributes its independent factor `p`, then the diluted field satisfies
the finite sequential criterion at density `a*p`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Fubini on a finite first coordinate, stated for real probabilities. -/
theorem measureReal_prod_eq_sum_sections
    {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (mu : Measure α) (nu : Measure β)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    (mu.prod nu).real A =
      ∑ x, mu.real {x} * nu.real (Prod.mk x ⁻¹' A) := by
  rw [measureReal_def, Measure.prod_apply hA, lintegral_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _hx
    rw [ENNReal.toReal_mul]
    simp only [measureReal_def]
    ring
  · intro x _hx
    exact ENNReal.mul_ne_top (measure_ne_top nu _) (measure_ne_top mu _)

/-- Product-space event corresponding to an exact prefix of the diluted configuration. -/
def dilutedProductPrefixEvent {n i : ℕ} (hi : i ≤ n)
    (s : Fin i → Bool) : Set (Set (Fin n) × Set (Fin n)) :=
  siteDilutionMap ⁻¹' finiteBoolPrefixEvent hi s

/-- The next original-field coordinate is open. -/
def originalProductCoordinateOpenEvent {n i : ℕ} (hi : i < n) :
    Set (Set (Fin n) × Set (Fin n)) :=
  {z | ⟨i, hi⟩ ∈ z.1}

/-- The next independent retention coordinate is open. -/
def retentionProductCoordinateOpenEvent {n i : ℕ} (hi : i < n) :
    Set (Set (Fin n) × Set (Fin n)) :=
  {z | ⟨i, hi⟩ ∈ z.2}

/-- Coordinates occurring in a Boolean prefix of length `i`. -/
def finiteBoolPrefixCoordinates {n i : ℕ} (_hi : i ≤ n) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.1 < i

theorem current_notMem_finiteBoolPrefixCoordinates {n i : ℕ} (hi : i < n) :
    (⟨i, hi⟩ : Fin n) ∉ finiteBoolPrefixCoordinates hi.le := by
  simp [finiteBoolPrefixCoordinates]

/-- Section of a diluted prefix event after fixing the original configuration. -/
def retentionPrefixSection {n i : ℕ} (y : Set (Fin n)) (hi : i ≤ n)
    (s : Fin i → Bool) : Set (Set (Fin n)) :=
  {z | y ∩ z ∈ finiteBoolPrefixEvent hi s}

theorem dependsOn_retentionPrefixSection {n i : ℕ}
    (y : Set (Fin n)) (hi : i ≤ n) (s : Fin i → Bool) :
    DependsOn (finiteBoolPrefixCoordinates hi) (retentionPrefixSection y hi s) := by
  classical
  intro z w hzw
  have hpref : boolPrefix hi (finiteSetBoolEquiv n (y ∩ z)) =
      boolPrefix hi (finiteSetBoolEquiv n (y ∩ w)) := by
    funext j
    have hj : Fin.castLE hi j ∈ finiteBoolPrefixCoordinates hi := by
      simp [finiteBoolPrefixCoordinates]
    have hcoord := hzw (Fin.castLE hi j) hj
    simp only [boolPrefix]
    change
      @decide (Fin.castLE hi j ∈ y ∩ z) (Classical.propDecidable _) =
        @decide (Fin.castLE hi j ∈ y ∩ w) (Classical.propDecidable _)
    apply decide_eq_decide.mpr
    simp only [Set.mem_inter_iff]
    exact and_congr Iff.rfl hcoord
  simp only [retentionPrefixSection, finiteBoolPrefixEvent, Set.mem_setOf_eq]
  rw [hpref]

/-- A diluted prefix section uses only earlier retention coordinates, so the current iid
retention bit contributes exactly one factor `p`. -/
theorem setBernoulli_real_retentionPrefixSection_inter_current
    {n i : ℕ} (p : I) (y : Set (Fin n)) (hi : i < n) (s : Fin i → Bool) :
    setBer((Set.univ : Set (Fin n)), p).real
        (retentionPrefixSection y hi.le s ∩
          {z : Set (Fin n) | ⟨i, hi⟩ ∈ z}) =
      (p : ℝ) * setBer((Set.univ : Set (Fin n)), p).real
        (retentionPrefixSection y hi.le s) := by
  let S : Set (Fin n) := finiteBoolPrefixCoordinates hi.le
  let T : Set (Fin n) := {⟨i, hi⟩}
  have hST : Disjoint S T := by
    rw [Set.disjoint_singleton_right]
    exact current_notMem_finiteBoolPrefixCoordinates hi
  have hA : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents S)]
      (retentionPrefixSection y hi.le s) := by
    exact (dependsOn_retentionPrefixSection y hi.le s
      ).measurableSet_generateFrom_coordinateEvents (by rfl)
  have hB : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents T)]
      {z : Set (Fin n) | ⟨i, hi⟩ ∈ z} := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨⟨i, hi⟩, Set.mem_singleton _, rfl⟩
  have hind : IndepSet (retentionPrefixSection y hi.le s)
      {z : Set (Fin n) | ⟨i, hi⟩ ∈ z}
      setBer((Set.univ : Set (Fin n)), p) :=
    (indep_generateFrom_coordinateEvents p hST).indepSet_of_measurableSet hA hB
  have hreal := congrArg ENNReal.toReal hind.measure_inter_eq_mul
  have hsingle := setBernoulli_real_superset_finset_univ
    ({⟨i, hi⟩} : Finset (Fin n)) p
  rw [ENNReal.toReal_mul] at hreal
  have hcoordinate :
      (setBer((Set.univ : Set (Fin n)), p)
        {z : Set (Fin n) | ⟨i, hi⟩ ∈ z}).toReal = (p : ℝ) := by
    change setBer((Set.univ : Set (Fin n)), p).real
      {z : Set (Fin n) | ⟨i, hi⟩ ∈ z} = (p : ℝ)
    simpa [Set.singleton_subset_iff] using hsingle
  rw [hcoordinate] at hreal
  simpa [measureReal_def, mul_comm] using hreal

theorem measurableSet_dilutedProductPrefixEvent {n i : ℕ}
    (hi : i ≤ n) (s : Fin i → Bool) :
    MeasurableSet (dilutedProductPrefixEvent hi s) :=
  (measurableSet_finiteBoolPrefixEvent hi s).preimage measurable_siteDilutionMap

theorem measurableSet_originalProductCoordinateOpenEvent {n i : ℕ}
    (hi : i < n) :
    MeasurableSet (originalProductCoordinateOpenEvent hi) := by
  exact (measurableSet_mem (⟨i, hi⟩ : Fin n)).preimage measurable_fst

theorem measurableSet_retentionProductCoordinateOpenEvent {n i : ℕ}
    (hi : i < n) :
    MeasurableSet (retentionProductCoordinateOpenEvent hi) := by
  exact (measurableSet_mem (⟨i, hi⟩ : Fin n)).preimage measurable_snd

theorem siteDilutionMap_preimage_prefixOpen {n i : ℕ}
    (hi : i < n) (s : Fin i → Bool) :
    siteDilutionMap ⁻¹' finiteBoolPrefixOpenEvent hi s =
      (dilutedProductPrefixEvent hi.le s ∩
        originalProductCoordinateOpenEvent hi) ∩
          retentionProductCoordinateOpenEvent hi := by
  ext z
  simp [finiteBoolPrefixOpenEvent, dilutedProductPrefixEvent,
    originalProductCoordinateOpenEvent, retentionProductCoordinateOpenEvent,
    siteDilutionMap, and_assoc]

/-- Ratio-free form of (7.117): conditioned on an exact diluted prefix, the next coordinate of
the undiluted field is open with mass at least `a`. -/
def HasLSSOriginalConditionalLowerBound {n : ℕ}
    (mu : Measure (Set (Fin n))) (p : I) (a : ℝ) : Prop :=
  ∀ i (hi : i < n) (s : Fin i → Bool),
    a * (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
        (dilutedProductPrefixEvent hi.le s) ≤
      (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
        (dilutedProductPrefixEvent hi.le s ∩
          originalProductCoordinateOpenEvent hi)

/-- The current retention bit is independent of the original field and all earlier diluted
prefix information.  It is separated from (7.117) so the later proof can use the iid coordinate
independence API directly. -/
def HasLSSRetentionFactorization {n : ℕ}
    (mu : Measure (Set (Fin n))) (p : I) : Prop :=
  ∀ i (hi : i < n) (s : Fin i → Bool),
    (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
        ((dilutedProductPrefixEvent hi.le s ∩
            originalProductCoordinateOpenEvent hi) ∩
          retentionProductCoordinateOpenEvent hi) =
      (p : ℝ) * (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
        (dilutedProductPrefixEvent hi.le s ∩
          originalProductCoordinateOpenEvent hi)

/-- The independent retention field automatically supplies the factorization required in
equation (7.116); it is not an additional hypothesis on the original field. -/
theorem hasLSSRetentionFactorization {n : ℕ}
    (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu] (p : I) :
    HasLSSRetentionFactorization mu p := by
  intro i hi s
  let idx : Fin n := ⟨i, hi⟩
  let prefixOriginal := dilutedProductPrefixEvent hi.le s ∩
    originalProductCoordinateOpenEvent hi
  let currentRetention := retentionProductCoordinateOpenEvent hi
  have hprefixOriginal : MeasurableSet prefixOriginal :=
    (measurableSet_dilutedProductPrefixEvent hi.le s).inter
      (measurableSet_originalProductCoordinateOpenEvent hi)
  have hcurrentRetention : MeasurableSet currentRetention :=
    measurableSet_retentionProductCoordinateOpenEvent hi
  rw [measureReal_prod_eq_sum_sections mu
      setBer((Set.univ : Set (Fin n)), p)
      (hprefixOriginal.inter hcurrentRetention),
    measureReal_prod_eq_sum_sections mu
      setBer((Set.univ : Set (Fin n)), p) hprefixOriginal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hy : idx ∈ y
  · have hsectionPrefix : Prod.mk y ⁻¹' prefixOriginal =
        retentionPrefixSection y hi.le s := by
      ext z
      simp [prefixOriginal, dilutedProductPrefixEvent,
        originalProductCoordinateOpenEvent, retentionPrefixSection,
        siteDilutionMap, idx, hy]
    have hsectionBoth : Prod.mk y ⁻¹' (prefixOriginal ∩ currentRetention) =
        retentionPrefixSection y hi.le s ∩
          {z : Set (Fin n) | idx ∈ z} := by
      ext z
      simp [prefixOriginal, currentRetention, dilutedProductPrefixEvent,
        originalProductCoordinateOpenEvent, retentionProductCoordinateOpenEvent,
        retentionPrefixSection, siteDilutionMap, idx, hy]
    rw [hsectionPrefix, hsectionBoth]
    rw [setBernoulli_real_retentionPrefixSection_inter_current p y hi s]
    ring
  · have hsectionPrefix : Prod.mk y ⁻¹' prefixOriginal = ∅ := by
      ext z
      simp [prefixOriginal, dilutedProductPrefixEvent,
        originalProductCoordinateOpenEvent, idx, hy]
    have hsectionBoth : Prod.mk y ⁻¹' (prefixOriginal ∩ currentRetention) = ∅ := by
      rw [Set.preimage_inter, hsectionPrefix, Set.empty_inter]
    rw [hsectionPrefix, hsectionBoth]
    simp

/-- Equations (7.116)--(7.117), finite ratio-free form. -/
theorem hasFiniteSequentialLowerBound_siteDilutionLaw {n : ℕ}
    (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu]
    (p : I) {a : ℝ}
    (hY : HasLSSOriginalConditionalLowerBound mu p a)
    (hZ : HasLSSRetentionFactorization mu p) :
    HasFiniteSequentialLowerBound (siteDilutionLaw mu p) (a * (p : ℝ)) := by
  rw [hasFiniteSequentialLowerBound_iff_event]
  intro i hi s
  rw [siteDilutionLaw,
    map_measureReal_apply measurable_siteDilutionMap
      (measurableSet_finiteBoolPrefixEvent hi.le s),
    map_measureReal_apply measurable_siteDilutionMap
      (measurableSet_finiteBoolPrefixOpenEvent hi s),
    siteDilutionMap_preimage_prefixOpen]
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  calc
    (a * (p : ℝ)) *
          (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
            (dilutedProductPrefixEvent hi.le s) =
        (p : ℝ) *
          (a * (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
            (dilutedProductPrefixEvent hi.le s)) := by ring
    _ ≤ (p : ℝ) *
          (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
            (dilutedProductPrefixEvent hi.le s ∩
              originalProductCoordinateOpenEvent hi) := by
      gcongr
      exact hY i hi s
    _ = (mu.prod setBer((Set.univ : Set (Fin n)), p)).real
          ((dilutedProductPrefixEvent hi.le s ∩
              originalProductCoordinateOpenEvent hi) ∩
            retentionProductCoordinateOpenEvent hi) := (hZ i hi s).symm

/-- Equation (7.116) with the fresh retention-bit factor discharged automatically. -/
theorem hasFiniteSequentialLowerBound_siteDilutionLaw_of_original {n : ℕ}
    (mu : Measure (Set (Fin n))) [IsProbabilityMeasure mu]
    (p : I) {a : ℝ}
    (hY : HasLSSOriginalConditionalLowerBound mu p a) :
    HasFiniteSequentialLowerBound (siteDilutionLaw mu p) (a * (p : ℝ)) :=
  hasFiniteSequentialLowerBound_siteDilutionLaw mu p hY
    (hasLSSRetentionFactorization mu p)

end Percolation
