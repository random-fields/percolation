import Percolation.Extensions.PeriodicMixed
import Percolation.Critical.Translation

/-!
# The cubic lattice as a periodic lattice

This file supplies the basic source example for the graph-theoretic lattice structure introduced
in Grimmett, Chapter 12, §12.1.  Integer translation acts freely and transitively, so the origin
is a one-vertex fundamental domain.
-/

namespace Percolation

open Set SimpleGraph

theorem cubicGraph_neighborSet_finite (d : ℕ) (x : Cubic d) :
    ((cubicGraph d).neighborSet x).Finite := by
  have hsubset : (cubicGraph d).neighborSet x ⊆
      Set.range (cubicStepFrom x) := by
    intro y hy
    rw [SimpleGraph.mem_neighborSet, cubicGraph_adj_iff_exists_stepFrom] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, rfl⟩
  exact Set.finite_range (cubicStepFrom x) |>.subset hsubset

theorem cubicGraph_connected (d : ℕ) : (cubicGraph d).Connected :=
  ⟨fun x y ↦ ⟨Classical.choose (exists_cubicWalk_length_eq_l1Dist d x y)⟩⟩

/-- The nearest-neighbor cubic graph with its standard free cocompact `ℤ^d` action. -/
noncomputable def cubicPeriodicLattice (d : ℕ) : PeriodicLattice (Cubic d) d where
  graph := cubicGraph d
  connected := cubicGraph_connected d
  neighborSet_finite := cubicGraph_neighborSet_finite d
  translate a := cubicTranslationIso cubicOrigin a
  translate_zero := by
    ext x i
    simp [cubicTranslationIso_apply, cubicTranslate, cubicOrigin]
  translate_add := by
    intro a b
    ext x i
    simp [cubicTranslationIso_apply, cubicTranslate, cubicOrigin]
    ring
  free := by
    intro a x hax
    funext i
    have hi := congrFun hax i
    simp [cubicTranslationIso_apply, cubicTranslate, cubicOrigin] at hi
    omega
  fundamentalDomain := {cubicOrigin}
  covers := by
    intro x
    refine ⟨x, cubicOrigin, by simp, ?_⟩
    ext i
    simp [cubicTranslationIso_apply, cubicTranslate, cubicOrigin]

@[simp]
theorem cubicPeriodicLattice_graph (d : ℕ) :
    (cubicPeriodicLattice d).graph = cubicGraph d := rfl

@[simp]
theorem cubicPeriodicLattice_translate_apply (d : ℕ) (a x : Cubic d) :
    (cubicPeriodicLattice d).translate a x = fun i ↦ x i + a i := by
  ext i
  change cubicTranslate cubicOrigin a x i = x i + a i
  simp [cubicTranslate, cubicOrigin]

@[simp]
theorem cubicPeriodicLattice_fundamentalDomain (d : ℕ) :
    (cubicPeriodicLattice d).fundamentalDomain = {cubicOrigin} := rfl

/-- The standard integer embedding makes the cubic lattice a geometric periodic lattice in the
precise sufficient sense recorded in `GeometricPeriodicLattice`. -/
noncomputable def cubicGeometricPeriodicLattice (d : ℕ) :
    GeometricPeriodicLattice (Cubic d) d where
  toPeriodicLattice := cubicPeriodicLattice d
  position x i := x i
  injective_position := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    change (x i : ℝ) = (y i : ℝ) at hi
    exact_mod_cast hi
  position_translate := by
    intro a x i
    rw [cubicPeriodicLattice_translate_apply]
    push_cast
    rfl
  proper_integer_boxes := by
    intro n
    apply (cubicBoxVertices d n).finite_toSet.subset
    intro x hx
    change x ∈ cubicBoxVertices d n
    rw [mem_cubicBoxVertices]
    change ∀ i : Fin d, -((n : ℕ) : ℝ) ≤ (x i : ℝ) ∧
      (x i : ℝ) ≤ (n : ℕ) at hx
    intro i
    have hi := hx i
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2
  edge_coordinate_span_bounded := by
    refine ⟨1, by norm_num, ?_⟩
    intro x y hxy i
    change (cubicGraph d).Adj x y at hxy
    rw [cubicGraph_adj_iff_exists_stepFrom] at hxy
    obtain ⟨⟨j, b⟩, rfl⟩ := hxy
    by_cases hij : i = j
    · subst i
      cases b <;> simp [cubicStepFrom, cubicDirectionIncrement]
    · simp [cubicStepFrom, cubicDirectionIncrement, hij]

@[simp]
theorem cubicGeometricPeriodicLattice_graph (d : ℕ) :
    (cubicGeometricPeriodicLattice d).graph = cubicGraph d := rfl

@[simp]
theorem cubicGeometricPeriodicLattice_position (d : ℕ) (x : Cubic d) (i : Fin d) :
    (cubicGeometricPeriodicLattice d).position x i = x i := rfl

end Percolation
