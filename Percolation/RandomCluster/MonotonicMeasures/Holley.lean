import Percolation.RandomCluster.MonotonicMeasures.Basic
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Holley's inequality for finite cube measures

Source: Grimmett, *The Random-Cluster Model* (2006), Chapter 2, Theorem 2.1.

The proof here packages Mathlib's finite-lattice Holley inequality for the
configuration lattice `Set ι`. A constant shift removes the nonnegativity
restriction on the increasing observable.
-/

namespace Percolation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

namespace FiniteCubeMeasure

/-- A uniform finite shift making an observable strictly positive everywhere. -/
noncomputable def positiveShift (X : Set ι → ℝ) : ℝ :=
  (∑ ω : Set ι, |X ω|) + 1

lemma lt_add_positiveShift (X : Set ι → ℝ) (ω : Set ι) :
    0 < X ω + positiveShift X := by
  classical
  have hterm : |X ω| ≤ ∑ η : Set ι, |X η| := by
    exact Finset.single_le_sum (fun η _ => abs_nonneg (X η)) (Finset.mem_univ ω)
  have hneg : -X ω ≤ |X ω| := neg_le_abs (X ω)
  dsimp [positiveShift]
  nlinarith

/-- Holley's inequality for nonnegative increasing observables. -/
lemma holley_nonneg (μ ν : FiniteCubeMeasure ι) (hH : HolleyCondition μ ν)
    {X : Set ι → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) (hX : IsIncreasingRandomVariable X) :
    μ.expect X ≤ ν.expect X := by
  classical
  rw [expect, expect]
  have hfg : (∑ a : Set ι, μ.mass a) = ∑ a : Set ι, ν.mass a := by
    rw [μ.sum_mass, ν.sum_mass]
  have h := _root_.holley μ.mass ν.mass X (fun ω => hX0 ω) (fun ω => μ.nonneg ω)
    (fun ω => ν.nonneg ω) (fun ω η hωη => hX hωη) hfg ?_
  · simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · intro a b
    simpa [HolleyCondition] using hH a b

/-- **Holley's inequality** (Grimmett, random-cluster book, Theorem 2.1). -/
theorem holley_inequality (μ ν : FiniteCubeMeasure ι) (hH : HolleyCondition μ ν)
    {X : Set ι → ℝ} (hX : IsIncreasingRandomVariable X) :
    μ.expect X ≤ ν.expect X := by
  classical
  let c := positiveShift X
  have hmono : IsIncreasingRandomVariable (fun ω => X ω + c) := by
    intro ω η hωη
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right (hX hωη) c
  have hnonneg : ∀ ω, 0 ≤ X ω + c := fun ω => le_of_lt (lt_add_positiveShift X ω)
  have h := holley_nonneg μ ν hH hnonneg hmono
  rw [show (fun ω => X ω + c) = fun ω => X ω - (-c) by funext ω; ring,
    expect_sub_const, expect_sub_const] at h
  linarith

theorem stochLE_of_holley (μ ν : FiniteCubeMeasure ι) (hH : HolleyCondition μ ν) :
    stochLE μ ν :=
  fun _ hX => holley_inequality μ ν hH hX

end FiniteCubeMeasure

end Percolation
