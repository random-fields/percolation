import Percolation.Critical.SupercriticalFiniteRadiusRate

/-!
# Truncated connectivity in the supercritical phase

This file introduces Grimmett's finite-cluster two-point function from (8.49) and proves the
radius comparisons (8.51), (8.55), and (8.57).  The reverse, gluing comparison needed for the
full logarithmic limit (8.54) is developed separately.
-/

namespace Percolation

open Set MeasureTheory Filter Topology
open scoped unitInterval

/-- The event that the origin and `x` belong to the same finite open cluster. -/
def truncatedConnectionEvent (d : ℕ) (x : Cubic d) : Set (EdgeConfiguration d) :=
  connectionEvent d cubicOrigin x ∩ finiteClusterEvent d

theorem measurableSet_truncatedConnectionEvent (d : ℕ) (x : Cubic d) :
    MeasurableSet (truncatedConnectionEvent d x) :=
  (measurableSet_connectionEvent d cubicOrigin x).inter
    (measurableSet_finiteClusterEvent d)

/-- Grimmett's truncated two-point connectivity `τᶠₚ(0,x)`. -/
noncomputable def truncatedTwoPointConnectivity
    (d : ℕ) (p : I) (x : Cubic d) : ℝ :=
  (bernoulliBondMeasure d p).real (truncatedConnectionEvent d x)

/-- Axis specialization `τᶠₚ(0,eₙ)` used in Theorem 8.53. -/
noncomputable def truncatedAxisConnectivity
    (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  truncatedTwoPointConnectivity d p (cubicAxisVertex d n)

theorem truncatedTwoPointConnectivity_nonneg
    (d : ℕ) (p : I) (x : Cubic d) :
    0 ≤ truncatedTwoPointConnectivity d p x := measureReal_nonneg

theorem truncatedTwoPointConnectivity_le_one
    (d : ℕ) (p : I) (x : Cubic d) :
    truncatedTwoPointConnectivity d p x ≤ 1 := measureReal_le_one

/-- Any finite connection from the origin to a vertex at `L∞` distance `n` first reaches the
box surface at radius `n`. -/
theorem truncatedConnectionEvent_subset_finiteBoxRadiusEvent
    {d : ℕ} {x : Cubic d} :
    truncatedConnectionEvent d x ⊆
      finiteBoxRadiusEvent d (cubicLInfDist cubicOrigin x) := by
  intro omega homega
  rcases homega with ⟨⟨w, hwOpen⟩, hfinite⟩
  refine ⟨?_, hfinite⟩
  obtain ⟨z, hzSurface, hzConn⟩ :=
    exists_open_walk_to_cubicBoxSurface_in_box w hwOpen le_rfl
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion]
  exact ⟨z, hzSurface, hzConn⟩

/-- Equation (8.51) before inserting Theorem 8.18's explicit bound. -/
theorem truncatedTwoPointConnectivity_le_finiteBoxRadiusProbability
    (d : ℕ) (p : I) (x : Cubic d) :
    truncatedTwoPointConnectivity d p x ≤
      finiteBoxRadiusProbability d p (cubicLInfDist cubicOrigin x) :=
  measureReal_mono truncatedConnectionEvent_subset_finiteBoxRadiusEvent

/-- Equation (8.57), specialized to the first coordinate axis. -/
theorem truncatedAxisConnectivity_le_finiteBoxRadiusProbability
    {d : ℕ} (hd : 0 < d) (p : I) (n : ℕ) :
    truncatedAxisConnectivity d p n ≤ finiteBoxRadiusProbability d p n := by
  have haxis : cubicLInfDist cubicOrigin (cubicAxisVertex d n) = n :=
    mem_cubicBoxSurface.mp (cubicAxisVertex_mem_boxSurface hd)
  simpa [truncatedAxisConnectivity, haxis] using
    truncatedTwoPointConnectivity_le_finiteBoxRadiusProbability
      d p (cubicAxisVertex d n)

/-- Endpoint-safe polynomial-exponential upper bound corresponding to (8.51). -/
theorem exists_truncatedTwoPointConnectivity_le_succ_pow_mul_exp_neg_rate
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : Cubic d,
      truncatedTwoPointConnectivity d p x ≤
        A * (((cubicLInfDist cubicOrigin x + 1 : ℕ) : ℝ) ^ d) *
          Real.exp (-(cubicLInfDist cubicOrigin x : ℝ) *
            finiteClusterRadiusDecayRate d p) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_finiteBoxRadiusProbability_le_succ_pow_mul_exp_neg_rate hd p hp0 hp1
  exact ⟨A, hA, fun x ↦
    (truncatedTwoPointConnectivity_le_finiteBoxRadiusProbability d p x).trans
      (hbound (cubicLInfDist cubicOrigin x))⟩

/-- Exact positive-radius source form of (8.55). -/
theorem exists_truncatedAxisConnectivity_le_pow_mul_exp_neg_rate
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 0 < n →
      truncatedAxisConnectivity d p n ≤
        A * ((n : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * finiteClusterRadiusDecayRate d p) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_finiteBoxRadiusProbability_le_pow_mul_exp_neg_rate hd p hp0 hp1
  refine ⟨A, hA, fun n hn ↦ ?_⟩
  exact (truncatedAxisConnectivity_le_finiteBoxRadiusProbability
    (Nat.zero_lt_of_lt hd) p n).trans (hbound n hn)

end Percolation
