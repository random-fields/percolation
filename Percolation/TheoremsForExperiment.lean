import Percolation.Planar.Inhomogeneous
import Percolation.Planar.RSWNumeric

/-!
# Theorem statements for the percolation experiment

This design-branch module collects three source-facing theorem targets requested for an
experiment.  Their proofs are intentionally left as `sorry`.  Existing square-lattice and RSW
definitions are reused; the homogeneous triangular model and Duminil-Copin's asymmetric
rectangle are named here because those exact source objects did not yet have dedicated APIs.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-! ## Grimmett, Theorem 3.7 -/

/-- Homogeneous Bernoulli bond percolation on the triangular lattice `T`, obtained by assigning
the same density to its horizontal, vertical, and north-east diagonal bonds. -/
noncomputable def triangularBondMeasure (p : I) : Measure TriangularConfiguration :=
  inhomogeneousTriangularBondMeasure p p p

/-- The probability that the origin cluster is infinite in homogeneous triangular-lattice bond
percolation. -/
noncomputable def triangularTheta (p : I) : ℝ :=
  (triangularBondMeasure p).real {omega | (triangularOpenCluster omega).Infinite}

/-- The bond critical probability of the triangular lattice, using Grimmett's supremum
normalization `sup {p : theta(p) = 0}`. -/
noncomputable def triangularCriticalProbability : ℝ :=
  sSup (((fun p : I ↦ (p : ℝ)) '' {p : I | triangularTheta p = 0}) : Set ℝ)

/-- **Grimmett, Percolation (2nd ed.), Theorem 3.7.**  The bond critical probability of the
triangular lattice is strictly smaller than that of the square lattice. -/
theorem grimmett_theorem_3_7 :
    triangularCriticalProbability < cubicCriticalProbability 2 := by
  sorry

/-! ## Grimmett, Theorem 11.70 -/

/-- The explicit lower-bound expression in Grimmett's equation (11.71). -/
noncomputable def grimmettRSWLowerBound (tau : ℝ) : ℝ :=
  (tau * (1 - Real.sqrt (1 - tau)) ^ 4) ^ 12

/-- **Grimmett, Percolation (2nd ed.), Theorem 11.70 (RSW).**  If `tau` is the probability
of a left-right crossing of `B(l)`, then the probability of an open circuit in
`B(3l) \ B(l)` surrounding the origin is at least the quantity in equation (11.71). -/
theorem grimmett_theorem_11_70 (p : I) (l : ℕ) (hl : 1 ≤ l) (tau : ℝ)
    (htau : rswSquareCrossingProbability p l = tau) :
    grimmettRSWLowerBound tau ≤ rswAnnulusOpenCircuitProbability p l := by
  sorry

/-! ## Duminil-Copin, Proposition 2.14 -/

/-- The vertices of `[-n,n] × [-n,2n]` in the square lattice. -/
noncomputable def duminilCopinRectangleVertices (n : ℕ) : Finset SquareVertex :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).product
    (Finset.Icc (-(n : ℤ)) (2 * (n : ℤ)))).map squareVertexEmbedding

/-- The bottom side `[-n,n] × {-n}` of Duminil-Copin's rectangle. -/
noncomputable def duminilCopinRectangleBottom (n : ℕ) : Finset SquareVertex :=
  (duminilCopinRectangleVertices n).filter fun x ↦ x 1 = -(n : ℤ)

/-- The top side `[-n,n] × {2n}` of Duminil-Copin's rectangle. -/
noncomputable def duminilCopinRectangleTop (n : ℕ) : Finset SquareVertex :=
  (duminilCopinRectangleVertices n).filter fun x ↦ x 1 = 2 * (n : ℤ)

/-- All square-lattice bonds whose endpoints lie in `[-n,n] × [-n,2n]`. -/
noncomputable def duminilCopinRectangleEdges (n : ℕ) : Finset SquareEdge :=
  (cubicBoxEdges 2 cubicOrigin (2 * n)).filter fun e ↦
    e.1.out.1 ∈ duminilCopinRectangleVertices n ∧
      e.1.out.2 ∈ duminilCopinRectangleVertices n

/-- The vertical open-crossing event `C_v([-n,n] × [-n,2n])`. -/
def duminilCopinVerticalCrossingEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ duminilCopinRectangleBottom n, ⋃ y ∈ duminilCopinRectangleTop n,
    connectionEventIn 2 (duminilCopinRectangleEdges n) x y

/-- The probability of Duminil-Copin's vertical rectangle-crossing event. -/
noncomputable def duminilCopinVerticalCrossingProbability (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real (duminilCopinVerticalCrossingEvent n)

/-- **Duminil-Copin, Graphical Representations of Lattice Spin Models, Proposition 2.14.**
At density `1/2`, the probability of a vertical crossing of `[-n,n] × [-n,2n]` is at least
`1/128` for every positive integer `n`. -/
theorem duminilCopin_proposition_2_14 (n : ℕ) (hn : 1 ≤ n) :
    (1 / 128 : ℝ) ≤ duminilCopinVerticalCrossingProbability squareHalfDensity n := by
  sorry

end Percolation
