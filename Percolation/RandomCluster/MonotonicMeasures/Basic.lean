import Percolation.Bernoulli.Increasing
import Percolation.RandomCluster.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Finite monotonic measures on the cube

Source: Grimmett, *The Random-Cluster Model* (2006), Chapter 2, "Monotonic
Measures", especially Sections 2.1-2.2.

This file sets up finite probability measures on the configuration cube
`Ω = {0,1}^E`, encoded as `Set ι` ordered by inclusion. It uses the generic monotonicity
API from `Percolation.Bernoulli.Increasing` and supports the Chapter 2 Holley and FKG
inequalities before specializing to random-cluster measures in Chapter 3.
-/

namespace Percolation

open scoped BigOperators

variable {ι : Type*}

theorem IsDecreasingEvent.indicator_isDecreasingRandomVariable {A : Set (Set ι)}
    (hA : IsDecreasingEvent A) :
    IsDecreasingRandomVariable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω) := by
  intro ω η hηω
  by_cases hη : η ∈ A
  · have hω : ω ∈ A := hA hηω hη
    simp [Set.indicator_of_mem hω, Set.indicator_of_mem hη]
  · by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω, Set.indicator_of_notMem hη]
    · simp [Set.indicator_of_notMem hω, Set.indicator_of_notMem hη]

theorem IsDecreasingRandomVariable.neg_isIncreasingRandomVariable {X : Set ι → ℝ}
    (hX : IsDecreasingRandomVariable X) :
    IsIncreasingRandomVariable (fun ω => -X ω) := by
  intro ω η hωη
  simpa using neg_le_neg (hX hωη)

theorem IsIncreasingRandomVariable.neg_isDecreasingRandomVariable {X : Set ι → ℝ}
    (hX : IsIncreasingRandomVariable X) :
    IsDecreasingRandomVariable (fun ω => -X ω) := by
  intro ω η hηω
  simpa using neg_le_neg (hX hηω)

variable [Fintype ι]

/-- A probability mass function on the finite cube `Set ι`. -/
structure FiniteCubeMeasure (ι : Type*) [Fintype ι] where
  /-- The mass of a configuration. -/
  mass : Set ι → ℝ
  /-- All configuration masses are nonnegative. -/
  nonneg : ∀ ω, 0 ≤ mass ω
  /-- The total mass is one. -/
  sum_mass : (∑ ω : Set ι, mass ω) = 1

namespace FiniteCubeMeasure

instance : CoeFun (FiniteCubeMeasure ι) (fun _ => Set ι → ℝ) where
  coe μ := μ.mass

/-- Expectation of a real observable on the finite cube. -/
noncomputable def expect (μ : FiniteCubeMeasure ι) (X : Set ι → ℝ) : ℝ :=
  ∑ ω : Set ι, μ ω * X ω

/-- Probability of an event on the finite cube. -/
noncomputable def prob (μ : FiniteCubeMeasure ι) (A : Set (Set ι)) : ℝ :=
  μ.expect (A.indicator fun _ => (1 : ℝ))

/-- Covariance under a finite cube measure. -/
noncomputable def covariance (μ : FiniteCubeMeasure ι) (X Y : Set ι → ℝ) : ℝ :=
  μ.expect (fun ω => X ω * Y ω) - μ.expect X * μ.expect Y

/-- Variance under a finite cube measure. -/
noncomputable def variance (μ : FiniteCubeMeasure ι) (X : Set ι → ℝ) : ℝ :=
  μ.covariance X X

/-- Strict positivity of all atoms. -/
def StrictPositive (μ : FiniteCubeMeasure ι) : Prop :=
  ∀ ω, 0 < μ ω

/-- Stochastic ordering of finite cube measures. -/
def stochLE (μ ν : FiniteCubeMeasure ι) : Prop :=
  ∀ X : Set ι → ℝ, IsIncreasingRandomVariable X → μ.expect X ≤ ν.expect X

/-- Grimmett's Holley condition (2.2). -/
def HolleyCondition (μ ν : FiniteCubeMeasure ι) : Prop :=
  ∀ ω η : Set ι, μ ω * ν η ≤ μ (ω ∩ η) * ν (ω ∪ η)

/-- The FKG lattice condition (2.15). -/
def FKGLatticeCondition (μ : FiniteCubeMeasure ι) : Prop :=
  HolleyCondition μ μ

/-- Positive association in expectation form. -/
def PositivelyAssociated (μ : FiniteCubeMeasure ι) : Prop :=
  ∀ X Y : Set ι → ℝ, IsIncreasingRandomVariable X → IsIncreasingRandomVariable Y →
    μ.expect X * μ.expect Y ≤ μ.expect (fun ω => X ω * Y ω)

theorem expect_const (μ : FiniteCubeMeasure ι) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  rw [expect]
  calc
    (∑ ω : Set ι, μ ω * c) = (∑ ω : Set ι, μ ω) * c := by rw [Finset.sum_mul]
    _ = c := by rw [μ.sum_mass, one_mul]

theorem expect_add (μ : FiniteCubeMeasure ι) (X Y : Set ι → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  rw [expect, expect, expect, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem expect_const_mul (μ : FiniteCubeMeasure ι) (c : ℝ) (X : Set ι → ℝ) :
    μ.expect (fun ω => c * X ω) = c * μ.expect X := by
  rw [expect, expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem expect_neg (μ : FiniteCubeMeasure ι) (X : Set ι → ℝ) :
    μ.expect (fun ω => -X ω) = -μ.expect X := by
  simpa using expect_const_mul μ (-1) X

theorem expect_finset_sum {α : Type*} (μ : FiniteCubeMeasure ι) (s : Finset α)
    (X : α → Set ι → ℝ) :
    μ.expect (fun ω => s.sum fun a => X a ω) = s.sum fun a => μ.expect (X a) := by
  rw [expect]
  calc
    (∑ ω : Set ι, μ ω * s.sum (fun a => X a ω))
        = ∑ ω : Set ι, s.sum fun a => μ ω * X a ω := by
            exact Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum]
    _ = s.sum (fun a => ∑ ω : Set ι, μ ω * X a ω) := by
            rw [Finset.sum_comm]
    _ = s.sum fun a => μ.expect (X a) := by
            exact Finset.sum_congr rfl fun _ _ => rfl

theorem expect_sum {α : Type*} [Fintype α] (μ : FiniteCubeMeasure ι)
    (X : α → Set ι → ℝ) :
    μ.expect (fun ω => ∑ a : α, X a ω) = ∑ a : α, μ.expect (X a) := by
  simpa using expect_finset_sum μ Finset.univ X

theorem covariance_sum_left {α : Type*} [Fintype α] (μ : FiniteCubeMeasure ι)
    (X : α → Set ι → ℝ) (Y : Set ι → ℝ) :
    μ.covariance (fun ω => ∑ a : α, X a ω) Y =
      ∑ a : α, μ.covariance (X a) Y := by
  rw [covariance]
  have hmul : (fun ω => (∑ a : α, X a ω) * Y ω) =
      fun ω => ∑ a : α, X a ω * Y ω := by
    funext ω
    rw [Finset.sum_mul]
  rw [hmul, expect_sum, expect_sum]
  simp [covariance, Finset.sum_sub_distrib, Finset.sum_mul]

theorem expect_sub_const (μ : FiniteCubeMeasure ι) (X : Set ι → ℝ) (c : ℝ) :
    μ.expect (fun ω => X ω - c) = μ.expect X - c := by
  have hfun : (fun ω => X ω - c) = fun ω => X ω + (fun _ => -c) ω := by
    funext ω
    ring
  rw [hfun, expect_add, expect_const]
  ring

theorem expect_add_const (μ : FiniteCubeMeasure ι) (X : Set ι → ℝ) (c : ℝ) :
    μ.expect (fun ω => X ω + c) = μ.expect X + c := by
  have hfun : (fun ω => X ω + c) = fun ω => X ω + (fun _ => c) ω := rfl
  rw [hfun, expect_add, expect_const]

theorem expect_mul_add_const (μ : FiniteCubeMeasure ι) (X Y : Set ι → ℝ) (c : ℝ) :
    μ.expect (fun ω => X ω * (Y ω + c)) =
      μ.expect (fun ω => X ω * Y ω) + c * μ.expect X := by
  rw [show (fun ω => X ω * (Y ω + c)) =
      fun ω => X ω * Y ω + c * X ω by funext ω; ring,
    expect_add, expect_const_mul]

theorem expect_pos_of_strictPositive_of_pos (μ : FiniteCubeMeasure ι)
    (hμ : μ.StrictPositive) {X : Set ι → ℝ} (hX : ∀ ω, 0 < X ω) :
    0 < μ.expect X := by
  classical
  rw [expect]
  refine Finset.sum_pos (fun ω _ => mul_pos (hμ ω) (hX ω)) ?_
  exact ⟨∅, Finset.mem_univ ∅⟩

end FiniteCubeMeasure

end Percolation
