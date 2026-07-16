import Percolation.Planar.Inhomogeneous

/-! Checked endpoint facts guarding against false strengthenings and totalized logarithms. -/

namespace Review.Chapter11Counterexamples

open Percolation Set
open scoped unitInterval

/-- Lean totalizes the logarithm at zero, so positive-density hypotheses cannot be dropped from
the logarithmic rate statements. -/
example : -Real.log 0 = 0 := by
  simp

/-- The zero density is outside the supercritical half-plane of Lemma 11.22. -/
example : ¬ (1 / 2 : ℝ) < ((0 : I) : ℝ) := by
  norm_num

/-- Density one is deliberately excluded from the finite-correlation-length and inhomogeneous
critical-surface statements. -/
example : ¬ (((1 : I) : ℝ) < 1) := by
  norm_num

/-- The source's tube-width premise excludes the generalized `k=0` endpoint. -/
example : ¬ 1 ≤ (0 : ℕ) := by
  omega

/-- At the potentially suspicious `l=0` endpoint, the three-halves crossing event is the whole
configuration space because its left and right faces coincide at the origin. -/
example : rswThreeHalvesCrossingEvent 0 = Set.univ := by
  ext omega
  constructor
  · simp
  · intro _h
    let x : SquareVertex := squareVertex 0 0
    have hxL : x ∈ squareRectangleLeft 0 0 := by simp [x, cubicOrigin]
    have hxR : x ∈ squareRectangleRight 0 0 := by simp [x, cubicOrigin]
    simp only [rswThreeHalvesCrossingEvent, Nat.mul_zero,
      squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
    refine ⟨x, hxL, x, hxR, SimpleGraph.Walk.nil, ?_, ?_⟩
    · simp [walkIsOpen]
    · intro e he
      simp [walkEdgeFinset, walkEdgeList] at he

end Review.Chapter11Counterexamples
