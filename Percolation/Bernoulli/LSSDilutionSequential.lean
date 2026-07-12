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

end Percolation
