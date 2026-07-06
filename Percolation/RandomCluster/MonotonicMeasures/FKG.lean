import Percolation.RandomCluster.MonotonicMeasures.Holley

/-!
# The FKG inequality for finite monotonic measures

Source: Grimmett, *The Random-Cluster Model* (2006), Chapter 2, Theorem 2.16.

This file proves the FKG inequality for strictly positive finite cube measures
satisfying the FKG lattice condition. The proof follows Grimmett's route:
shift the second observable to be strictly positive, tilt the measure by this
observable, verify Holley's condition for the tilted measure, and apply Holley's
inequality.
-/

namespace Percolation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

namespace FiniteCubeMeasure

/-- Tilt a finite cube measure by a nonnegative observable with positive expectation. -/
noncomputable def tiltBy (μ : FiniteCubeMeasure ι) (Y : Set ι → ℝ)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hEY : 0 < μ.expect Y) : FiniteCubeMeasure ι where
  mass := fun ω => μ ω * Y ω / μ.expect Y
  nonneg := by
    intro ω
    exact div_nonneg (mul_nonneg (μ.nonneg ω) (hY0 ω)) (le_of_lt hEY)
  sum_mass := by
    have hEY' : 0 < ∑ η : Set ι, μ η * Y η := by
      simpa [expect] using hEY
    calc
      (∑ ω : Set ι, μ ω * Y ω / μ.expect Y)
          = (∑ ω : Set ι, μ ω * Y ω) / μ.expect Y := by
              rw [Finset.sum_div]
      _ = 1 := by
          change (∑ ω : Set ι, μ ω * Y ω) / (∑ η : Set ι, μ η * Y η) = 1
          field_simp [ne_of_gt hEY']

theorem tiltBy_expect (μ : FiniteCubeMeasure ι) (Y X : Set ι → ℝ)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hEY : 0 < μ.expect Y) :
    (tiltBy μ Y hY0 hEY).expect X = μ.expect (fun ω => X ω * Y ω) / μ.expect Y := by
  change (∑ ω : Set ι, (μ ω * Y ω / μ.expect Y) * X ω) =
    (∑ ω : Set ι, μ ω * (X ω * Y ω)) / μ.expect Y
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem holleyCondition_tiltBy (μ : FiniteCubeMeasure ι) {Y : Set ι → ℝ}
    (hFKG : FKGLatticeCondition μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hY : IsIncreasingRandomVariable Y) (hEY : 0 < μ.expect Y) :
    HolleyCondition μ (tiltBy μ Y hY0 hEY) := by
  intro ω η
  have hbase : μ ω * μ η ≤ μ (ω ∩ η) * μ (ω ∪ η) := hFKG ω η
  have hYle : Y η ≤ Y (ω ∪ η) := hY Set.subset_union_right
  have hnum₁ : μ ω * μ η * Y η ≤ μ (ω ∩ η) * μ (ω ∪ η) * Y η :=
    mul_le_mul_of_nonneg_right hbase (hY0 η)
  have hnum₂ : μ (ω ∩ η) * μ (ω ∪ η) * Y η ≤
      μ (ω ∩ η) * μ (ω ∪ η) * Y (ω ∪ η) := by
    exact mul_le_mul_of_nonneg_left hYle
      (mul_nonneg (μ.nonneg (ω ∩ η)) (μ.nonneg (ω ∪ η)))
  have hnum := hnum₁.trans hnum₂
  have hdiv := div_le_div_of_nonneg_right hnum (le_of_lt hEY)
  calc
    μ ω * tiltBy μ Y hY0 hEY η = (μ ω * μ η * Y η) / μ.expect Y := by
      simp [tiltBy]
      ring
    _ ≤ (μ (ω ∩ η) * μ (ω ∪ η) * Y (ω ∪ η)) / μ.expect Y := hdiv
    _ = μ (ω ∩ η) * tiltBy μ Y hY0 hEY (ω ∪ η) := by
      simp [tiltBy]
      ring

theorem fkg_positive_right (μ : FiniteCubeMeasure ι) (hμ : μ.StrictPositive)
    (hFKG : FKGLatticeCondition μ) {X Y : Set ι → ℝ}
    (hX : IsIncreasingRandomVariable X) (hYpos : ∀ ω, 0 < Y ω)
    (hY : IsIncreasingRandomVariable Y) :
    μ.expect X * μ.expect Y ≤ μ.expect (fun ω => X ω * Y ω) := by
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => le_of_lt (hYpos ω)
  have hEY : 0 < μ.expect Y := expect_pos_of_strictPositive_of_pos μ hμ hYpos
  let ν := tiltBy μ Y hY0 hEY
  have hH : HolleyCondition μ ν := holleyCondition_tiltBy μ hFKG hY0 hY hEY
  have hstoch := holley_inequality μ ν hH hX
  have hν : ν.expect X = μ.expect (fun ω => X ω * Y ω) / μ.expect Y := by
    simpa [ν] using tiltBy_expect μ Y X hY0 hEY
  rw [hν] at hstoch
  have hmul := mul_le_mul_of_nonneg_right hstoch (le_of_lt hEY)
  field_simp [ne_of_gt hEY] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- **The FKG inequality** (Grimmett, random-cluster book, Theorem 2.16). -/
theorem fkg (μ : FiniteCubeMeasure ι) (hμ : μ.StrictPositive)
    (hFKG : FKGLatticeCondition μ) {X Y : Set ι → ℝ}
    (hX : IsIncreasingRandomVariable X) (hY : IsIncreasingRandomVariable Y) :
    μ.expect X * μ.expect Y ≤ μ.expect (fun ω => X ω * Y ω) := by
  classical
  let c := positiveShift Y
  have hYpos : ∀ ω, 0 < Y ω + c := fun ω => lt_add_positiveShift Y ω
  have hYmono : IsIncreasingRandomVariable (fun ω => Y ω + c) := by
    intro ω η hωη
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right (hY hωη) c
  have h := fkg_positive_right μ hμ hFKG hX hYpos hYmono
  rw [expect_add_const, expect_mul_add_const] at h
  nlinarith

theorem positivelyAssociated_of_fkg (μ : FiniteCubeMeasure ι) (hμ : μ.StrictPositive)
    (hFKG : FKGLatticeCondition μ) : PositivelyAssociated μ := by
  intro X Y hX hY
  exact fkg μ hμ hFKG hX hY

/-- Event form of the FKG inequality, equation (2.18). -/
theorem prob_fkg (μ : FiniteCubeMeasure ι) (hμ : μ.StrictPositive)
    (hFKG : FKGLatticeCondition μ) {A B : Set (Set ι)}
    (hA : IsIncreasingEvent A) (hB : IsIncreasingEvent B) :
    μ.prob A * μ.prob B ≤ μ.prob (A ∩ B) := by
  have h := fkg μ hμ hFKG hA.indicator_isIncreasingRandomVariable
    hB.indicator_isIncreasingRandomVariable
  have hmul : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      B.indicator (fun _ => (1 : ℝ)) ω) = (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]
  simpa [prob, hmul] using h

end FiniteCubeMeasure

end Percolation
