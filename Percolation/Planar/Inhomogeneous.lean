import Percolation.Bernoulli.Inhomogeneous
import Percolation.Planar.SupercriticalCrossings

/-!
# Inhomogeneous planar percolation

This file supplies concrete product measures for the inhomogeneous square and triangular
lattices used at the end of Grimmett Chapter 11.  The common coordinate-dependent product law
is defined in `Percolation.Bernoulli.Inhomogeneous`.  The critical-surface conclusions themselves
are external-reference axioms: Grimmett states them without proofs and refers to the original
star--triangle literature.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

/-- A square-lattice edge is horizontal when its endpoints have the same second coordinate. -/
def squareEdgeIsHorizontal (e : SquareEdge) : Prop :=
  e.1.out.1 1 = e.1.out.2 1

/-- Horizontal/vertical density profile on the square lattice. -/
noncomputable def inhomogeneousSquareEdgeDensity (pₕ pᵥ : I) (e : SquareEdge) : I :=
  by
    classical
    exact if squareEdgeIsHorizontal e then pₕ else pᵥ

/-- Product law for inhomogeneous square-lattice bond percolation. -/
noncomputable def inhomogeneousSquareBondMeasure (pₕ pᵥ : I) :
    Measure (EdgeConfiguration 2) :=
  inhomogeneousSetBernoulli (inhomogeneousSquareEdgeDensity pₕ pᵥ)

/-- Inhomogeneous square-lattice percolation probability. -/
noncomputable def inhomogeneousSquareTheta (pₕ pᵥ : I) : ℝ :=
  (inhomogeneousSquareBondMeasure pₕ pᵥ).real
    {ω | (cubicOpenCluster 2 ω).Infinite}

/-- The square critical polynomial `φ(p)=pₕ+pᵥ`. -/
def inhomogeneousSquareCriticalPolynomial (pₕ pᵥ : I) : ℝ :=
  (pₕ : ℝ) + pᵥ

def triangularDiagonalStep (x y : SquareVertex) : Prop :=
  y = fun i ↦ x i + 1

/-- The positive generating steps of the triangular lattice. -/
def triangularStep (x y : SquareVertex) : Prop :=
  cubicStep 2 x y ∨ triangularDiagonalStep x y

/-- The triangular lattice obtained by adding north-east diagonals to the square lattice. -/
def triangularGraph : SimpleGraph SquareVertex :=
  SimpleGraph.fromRel triangularStep

/-- Bond coordinates of the triangular lattice. -/
abbrev TriangularEdge := triangularGraph.edgeSet

/-- Triangular-lattice bond configurations. -/
abbrev TriangularConfiguration := Set TriangularEdge

/-- A triangular edge is horizontal if its second coordinates agree. -/
def triangularEdgeIsHorizontal (e : TriangularEdge) : Prop :=
  e.1.out.1 1 = e.1.out.2 1

/-- A triangular edge is vertical if its first coordinates agree. -/
def triangularEdgeIsVertical (e : TriangularEdge) : Prop :=
  e.1.out.1 0 = e.1.out.2 0

/-- Horizontal/vertical/diagonal density profile on the triangular lattice. -/
noncomputable def inhomogeneousTriangularEdgeDensity
    (pₕ pᵥ pₑ : I) (e : TriangularEdge) : I :=
  by
    classical
    exact if triangularEdgeIsHorizontal e then pₕ
      else if triangularEdgeIsVertical e then pᵥ
      else pₑ

/-- Product law for inhomogeneous triangular-lattice bond percolation. -/
noncomputable def inhomogeneousTriangularBondMeasure (pₕ pᵥ pₑ : I) :
    Measure TriangularConfiguration :=
  inhomogeneousSetBernoulli (inhomogeneousTriangularEdgeDensity pₕ pᵥ pₑ)

/-- The open subgraph of a triangular-lattice configuration. -/
def triangularOpenGraph (ω : TriangularConfiguration) : SimpleGraph SquareVertex where
  Adj x y := ∃ h : triangularGraph.Adj x y,
    (⟨s(x, y), (SimpleGraph.mem_edgeSet triangularGraph).2 h⟩ : TriangularEdge) ∈ ω
  symm := by
    rintro x y ⟨h, hω⟩
    let h' := triangularGraph.symm h
    refine ⟨h', ?_⟩
    simpa only [Sym2.eq_swap] using hω
  loopless := by
    exact ⟨fun x h ↦ triangularGraph.loopless.irrefl x h.1⟩

/-- The open cluster of the origin in a triangular configuration. -/
def triangularOpenCluster (ω : TriangularConfiguration) : Set SquareVertex :=
  {x | Nonempty ((triangularOpenGraph ω).Walk cubicOrigin x)}

/-- Inhomogeneous triangular-lattice percolation probability. -/
noncomputable def inhomogeneousTriangularTheta (pₕ pᵥ pₑ : I) : ℝ :=
  (inhomogeneousTriangularBondMeasure pₕ pᵥ pₑ).real
    {ω | (triangularOpenCluster ω).Infinite}

/-- The triangular critical polynomial
`psi(p)=pₕ+pᵥ+pₑ-pₕpᵥpₑ`. -/
def inhomogeneousTriangularCriticalPolynomial (pₕ pᵥ pₑ : I) : ℝ :=
  (pₕ : ℝ) + pᵥ + pₑ - (pₕ : ℝ) * pᵥ * pₑ

end Percolation
