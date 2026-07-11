import Percolation.Critical.Regions

/-!
# Finite thick-slab connection regions

This file defines the two finite regions in Grimmett (7.76)--(7.77):

* `finiteThickSlabSVertices d n L = [-n,n]² × [0,L]^(d-2)`;
* `finiteThickSlabTVertices d n L = [-n,n]^(d-1) × [0,L]`.

They are represented as finsets so that later FKG products, finite-energy modifications, and
uniform connection estimates have explicit finite supports.  The public membership lemmas are
the source-facing coordinate descriptions and remain meaningful outside the source range
`3 ≤ d`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The finite thick slab `S_n(L) = [-n,n]² × [0,L]^(d-2)` from (7.76). -/
noncomputable def finiteThickSlabSVertices (d n L : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin (max n L)).filter fun x ↦
    ∀ i : Fin d,
      if i.val < 2 then (x i).natAbs ≤ n else 0 ≤ x i ∧ x i ≤ L

/-- The finite thick slab `T_n(L) = [-n,n]^(d-1) × [0,L]` from (7.77). -/
noncomputable def finiteThickSlabTVertices (d n L : ℕ) : Finset (Cubic d) :=
  (cubicMetricBox d cubicOrigin (max n L)).filter fun x ↦
    ∀ i : Fin d,
      if i.val + 1 = d then 0 ≤ x i ∧ x i ≤ L else (x i).natAbs ≤ n

@[simp]
theorem mem_finiteThickSlabSVertices_iff {d n L : ℕ} {x : Cubic d} :
    x ∈ finiteThickSlabSVertices d n L ↔
      ∀ i : Fin d,
        if i.val < 2 then (x i).natAbs ≤ n else 0 ≤ x i ∧ x i ≤ L := by
  classical
  rw [finiteThickSlabSVertices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [mem_cubicMetricBox]
    intro i
    simp only [cubicOrigin, zero_sub, zero_add]
    have hi := h i
    split at hi
    · have habs : |x i| ≤ (n : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact Int.ofNat_le.mpr hi
      have hnmax : (n : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_left n L
      exact ⟨(neg_le_neg hnmax).trans (neg_le_of_abs_le habs),
        (le_of_abs_le habs).trans hnmax⟩
    · have hLmax : (L : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_right n L
      constructor <;> omega

@[simp]
theorem mem_finiteThickSlabTVertices_iff {d n L : ℕ} {x : Cubic d} :
    x ∈ finiteThickSlabTVertices d n L ↔
      ∀ i : Fin d,
        if i.val + 1 = d then 0 ≤ x i ∧ x i ≤ L else (x i).natAbs ≤ n := by
  classical
  rw [finiteThickSlabTVertices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [mem_cubicMetricBox]
    intro i
    simp only [cubicOrigin, zero_sub, zero_add]
    have hi := h i
    split at hi
    · have hLmax : (L : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_right n L
      constructor <;> omega
    · have habs : |x i| ≤ (n : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact Int.ofNat_le.mpr hi
      have hnmax : (n : ℤ) ≤ (max n L : ℕ) := by
        exact_mod_cast Nat.le_max_left n L
      exact ⟨(neg_le_neg hnmax).trans (neg_le_of_abs_le habs),
        (le_of_abs_le habs).trans hnmax⟩

theorem finiteThickSlabSVertices_subset_box (d n L : ℕ) :
    (finiteThickSlabSVertices d n L : Set (Cubic d)) ⊆
      cubicMetricBox d cubicOrigin (max n L) := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem finiteThickSlabTVertices_subset_box (d n L : ℕ) :
    (finiteThickSlabTVertices d n L : Set (Cubic d)) ⊆
      cubicMetricBox d cubicOrigin (max n L) := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- Open connection constrained to `S_n(L)`. -/
def finiteThickSlabSConnectionEvent
    (d n L : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  connectionEventWithinVertices d (finiteThickSlabSVertices d n L : Set (Cubic d)) x y

/-- Open connection constrained to `T_n(L)`. -/
def finiteThickSlabTConnectionEvent
    (d n L : ℕ) (x y : Cubic d) : Set (EdgeConfiguration d) :=
  connectionEventWithinVertices d (finiteThickSlabTVertices d n L : Set (Cubic d)) x y

theorem measurableSet_finiteThickSlabSConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    MeasurableSet (finiteThickSlabSConnectionEvent d n L x y) :=
  measurableSet_connectionEventWithinVertices d _ x y

theorem measurableSet_finiteThickSlabTConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    MeasurableSet (finiteThickSlabTConnectionEvent d n L x y) :=
  measurableSet_connectionEventWithinVertices d _ x y

theorem isIncreasingEvent_finiteThickSlabSConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    IsIncreasingEvent (finiteThickSlabSConnectionEvent d n L x y) :=
  isIncreasingEvent_connectionEventWithinVertices d _ x y

theorem isIncreasingEvent_finiteThickSlabTConnectionEvent
    (d n L : ℕ) (x y : Cubic d) :
    IsIncreasingEvent (finiteThickSlabTConnectionEvent d n L x y) :=
  isIncreasingEvent_connectionEventWithinVertices d _ x y

@[simp]
theorem finiteThickSlabSConnectionEvent_self {d n L : ℕ} {x : Cubic d}
    (hx : x ∈ finiteThickSlabSVertices d n L) :
    finiteThickSlabSConnectionEvent d n L x x = Set.univ := by
  ext ω
  constructor
  · exact fun _ ↦ Set.mem_univ ω
  · intro _
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simpa using hx⟩

@[simp]
theorem finiteThickSlabTConnectionEvent_self {d n L : ℕ} {x : Cubic d}
    (hx : x ∈ finiteThickSlabTVertices d n L) :
    finiteThickSlabTConnectionEvent d n L x x = Set.univ := by
  ext ω
  constructor
  · exact fun _ ↦ Set.mem_univ ω
  · intro _
    exact ⟨SimpleGraph.Walk.nil, by simp [walkIsOpen], by simpa using hx⟩

/-- Source-facing lower-bound package for the two conclusions (7.79)--(7.80). -/
def UniformFiniteSlabConnectionLowerBound
    (d : ℕ) (p : I) (L : ℕ) (δ : ℝ) : Prop :=
  (∀ n, 1 ≤ n → ∀ x ∈ finiteThickSlabSVertices d n L,
    ∀ y ∈ finiteThickSlabSVertices d n L,
      δ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabSConnectionEvent d n L x y)) ∧
  (∀ n, 1 ≤ n → ∀ x ∈ finiteThickSlabTVertices d n L,
    ∀ y ∈ finiteThickSlabTVertices d n L,
      δ ≤ (bernoulliBondMeasure d p).real
        (finiteThickSlabTConnectionEvent d n L x y))

end Percolation
