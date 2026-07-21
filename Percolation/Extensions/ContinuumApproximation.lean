import Percolation.Extensions.ContinuumCubes

/-!
# The finite-range lattice used to approximate continuum percolation

This file gives a literal indexed-cube version of Grimmett (12.37).  A vertex `x : Cubic d`
represents the cube of side `1/n` centred at `x/n`; two distinct vertices are adjacent when some
point of one cube is within Euclidean distance two of some point of the other.
-/

namespace Percolation

open Set
open scoped BigOperators

/-- The centre of the cube indexed by `x`, at mesh `1/n`. -/
noncomputable def continuumCubeCenter {d : ℕ} (n : ℕ) (x : Cubic d) : Fin d → ℝ :=
  fun i ↦ (x i : ℝ) / n

/-- The half-open elementary cube of side `1/n` centred at `x/n`.  The `0<n` hypothesis in all
source-facing uses ensures that this has the intended orientation. -/
noncomputable def continuumElementaryCube {d : ℕ} (n : ℕ) (x : Cubic d) :
    Set (Fin d → ℝ) :=
  {u | ∀ i, continuumCubeCenter n x i - 1 / (2 * n) ≤ u i ∧
      u i < continuumCubeCenter n x i + 1 / (2 * n)}

@[simp]
theorem mem_continuumElementaryCube {d : ℕ} (n : ℕ) (x : Cubic d)
    (u : Fin d → ℝ) :
    u ∈ continuumElementaryCube n x ↔
      ∀ i, continuumCubeCenter n x i - 1 / (2 * n) ≤ u i ∧
        u i < continuumCubeCenter n x i + 1 / (2 * n) := Iff.rfl

/-- Euclidean distance on coordinate vectors, written explicitly so the product type does not
silently select the `L∞` metric. -/
noncomputable def coordinateEuclideanDist {d : ℕ} (u v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, (u i - v i) ^ 2)

theorem coordinateEuclideanDist_comm {d : ℕ} (u v : Fin d → ℝ) :
    coordinateEuclideanDist u v = coordinateEuclideanDist v u := by
  unfold coordinateEuclideanDist
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The adjacency relation in (12.37), on integer cube indices. -/
def continuumApproximationAdj (d n : ℕ) (x y : Cubic d) : Prop :=
  x ≠ y ∧ ∃ u ∈ continuumElementaryCube n x,
    ∃ v ∈ continuumElementaryCube n y, coordinateEuclideanDist u v ≤ 2

theorem continuumApproximationAdj_symm {d n : ℕ} {x y : Cubic d} :
    continuumApproximationAdj d n x y → continuumApproximationAdj d n y x := by
  rintro ⟨hxy, u, hu, v, hv, huv⟩
  exact ⟨hxy.symm, v, hv, u, hu,
    (coordinateEuclideanDist_comm v u).le.trans huv⟩

theorem continuumApproximationAdj_irrefl {d n : ℕ} (x : Cubic d) :
    ¬continuumApproximationAdj d n x x := by
  intro h
  exact h.1 rfl

/-- Grimmett's discretization lattice `Lₙ`. -/
def continuumApproximationGraph (d n : ℕ) : SimpleGraph (Cubic d) where
  Adj := continuumApproximationAdj d n
  symm _ _ := continuumApproximationAdj_symm
  loopless := ⟨fun x ↦ continuumApproximationAdj_irrefl (d := d) (n := n) x⟩

@[simp]
theorem continuumApproximationGraph_adj {d n : ℕ} {x y : Cubic d} :
    (continuumApproximationGraph d n).Adj x y ↔
      x ≠ y ∧ ∃ u ∈ continuumElementaryCube n x,
        ∃ v ∈ continuumElementaryCube n y, coordinateEuclideanDist u v ≤ 2 := Iff.rfl

/-- Every positive-mesh elementary cube contains its centre. -/
theorem continuumCubeCenter_mem_elementaryCube {d n : ℕ} (hn : 0 < n)
    (x : Cubic d) :
    continuumCubeCenter n x ∈ continuumElementaryCube n x := by
  intro i
  have hpos : 0 < (1 : ℝ) / (2 * n) := by positivity
  constructor <;> dsimp [continuumCubeCenter] <;> linarith

/-- If the cube centres themselves are within distance two, their vertices are adjacent. -/
theorem continuumApproximationGraph_adj_of_centerDist_le {d n : ℕ} (hn : 0 < n)
    {x y : Cubic d} (hxy : x ≠ y)
    (hdist : coordinateEuclideanDist (continuumCubeCenter n x)
      (continuumCubeCenter n y) ≤ 2) :
    (continuumApproximationGraph d n).Adj x y := by
  exact ⟨hxy, continuumCubeCenter n x,
    continuumCubeCenter_mem_elementaryCube hn x,
    continuumCubeCenter n y, continuumCubeCenter_mem_elementaryCube hn y, hdist⟩

theorem coordinateEuclideanDist_center_step {d n : ℕ} (hn : 0 < n)
    (x : Cubic d) (a : CubicDirection d) :
    coordinateEuclideanDist (continuumCubeCenter n x)
      (continuumCubeCenter n (cubicStepFrom x a)) = 1 / n := by
  rcases a with ⟨i, b⟩
  unfold coordinateEuclideanDist
  have hsum :
      (∑ j : Fin d, (continuumCubeCenter n x j -
          continuumCubeCenter n (cubicStepFrom x (i, b)) j) ^ 2) =
        (1 / (n : ℝ)) ^ 2 := by
    rw [Finset.sum_eq_single i]
    · unfold continuumCubeCenter cubicStepFrom cubicDirectionIncrement
      simp
      split <;> ring
    · intro j _hj hji
      simp [continuumCubeCenter, cubicStepFrom, Function.update_of_ne hji]
    · simp
  rw [hsum, Real.sqrt_sq_eq_abs, abs_of_pos]
  positivity

/-- The approximation graph contains all nearest-neighbour cubic edges. -/
theorem cubicGraph_le_continuumApproximationGraph {d n : ℕ} (hn : 0 < n) :
    cubicGraph d ≤ continuumApproximationGraph d n := by
  intro x y hxy
  rw [cubicGraph_adj_iff_exists_stepFrom] at hxy
  obtain ⟨a, ha⟩ := hxy
  subst y
  apply continuumApproximationGraph_adj_of_centerDist_le hn
  · exact (cubicGraph_adj_stepFrom x a).ne
  · rw [coordinateEuclideanDist_center_step hn]
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_one hnpos).2 hnreal |>.trans (by norm_num)

end Percolation
