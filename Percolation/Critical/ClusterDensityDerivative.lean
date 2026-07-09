/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Percolation.Critical.LatticeAnimals
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiability of the open-cluster density series

Source: Grimmett, *Percolation* (2nd ed., 1999), §4.3, pp. 84–86
(source id `grimmett-percolation-1999`).

Grimmett's Theorem 4.31 proves that the number `κ(p)` of open clusters per vertex is continuously
differentiable on `[0,1]`, and equation (4.32) identifies its derivative with the term-by-term
derivative of the lattice-animal series (4.18). This file formalizes that series, its exact formal
derivative, and the uniform-convergence theorem which produces a `C¹` sum.

The headline theorem `clusterDensitySeries_contDiffOn_unitInterval` deliberately exposes the
remaining analytic input as a summable uniform majorant for the derivative terms on a
neighbourhood of `[0,1]`. In the book, the lattice-animal estimate of Theorem 4.20 proves the
corresponding uniform convergence in the interior, while equations (4.36)–(4.37) handle the two
endpoints separately. No project axiom is introduced here.

## Main results

* `animalSeriesTerm_hasDerivAt`: formal term-by-term differentiation, exactly equation (4.32).
* `clusterDensitySeries_contDiffOn_unitInterval`: the uniform-limit `C¹` theorem for the animal
  expansion, including the derivative-series identity at every point of `[0,1]`.
-/

open scoped BigOperators Topology
open Set

namespace Percolation

noncomputable section

/-- An index `(n,m,b)` for animals with `n` vertices, `m` occupied bonds, and `b` boundary bonds. -/
structure AnimalSeriesIndex where
  vertices : ℕ
  occupied : ℕ
  boundary : ℕ
  deriving DecidableEq

/-- The `(n,m,b)` summand `n⁻¹ aₙₘᵦ pᵐ (1-p)ᵇ` in Grimmett's equation (4.18). -/
def animalSeriesTerm (a : ℕ → ℕ → ℕ → ℕ) (i : AnimalSeriesIndex) (p : ℝ) : ℝ :=
  (a i.vertices i.occupied i.boundary : ℝ) / i.vertices *
    p ^ i.occupied * (1 - p) ^ i.boundary

/-- The formal derivative of `animalSeriesTerm`, matching the summand in equation (4.32). -/
def animalSeriesTermDerivative (a : ℕ → ℕ → ℕ → ℕ)
    (i : AnimalSeriesIndex) (p : ℝ) : ℝ :=
  (a i.vertices i.occupied i.boundary : ℝ) / i.vertices *
    ((i.occupied : ℝ) * p ^ (i.occupied - 1) * (1 - p) ^ i.boundary -
      (i.boundary : ℝ) * p ^ i.occupied * (1 - p) ^ (i.boundary - 1))

/-- The lattice-animal expansion of the open-cluster density from equation (4.18). -/
def clusterDensitySeries (a : ℕ → ℕ → ℕ → ℕ) (p : ℝ) : ℝ :=
  ∑' i : AnimalSeriesIndex, animalSeriesTerm a i p

/-- The term-by-term derivative series displayed in equation (4.32). -/
def clusterDensityDerivativeSeries (a : ℕ → ℕ → ℕ → ℕ) (p : ℝ) : ℝ :=
  ∑' i : AnimalSeriesIndex, animalSeriesTermDerivative a i p

/-- Every animal-series summand has exactly the formal derivative in Grimmett's equation (4.32). -/
theorem animalSeriesTerm_hasDerivAt (a : ℕ → ℕ → ℕ → ℕ)
    (i : AnimalSeriesIndex) (p : ℝ) :
    HasDerivAt (animalSeriesTerm a i) (animalSeriesTermDerivative a i p) p := by
  have hp := (hasDerivAt_id p).pow i.occupied
  have hq := ((hasDerivAt_id p).neg.add_const 1).pow i.boundary
  unfold animalSeriesTerm animalSeriesTermDerivative
  convert (hp.mul hq).const_mul
    ((a i.vertices i.occupied i.boundary : ℝ) / i.vertices) using 1
  · funext y
    simp only [Function.id_def, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply]
    ring
  · simp only [Function.id_def, Pi.pow_apply, Pi.neg_apply]
    ring

/-- The formal derivative of each animal-series summand is a continuous polynomial. -/
theorem animalSeriesTermDerivative_continuous (a : ℕ → ℕ → ℕ → ℕ)
    (i : AnimalSeriesIndex) : Continuous (animalSeriesTermDerivative a i) := by
  unfold animalSeriesTermDerivative
  fun_prop

/-- **Grimmett, Theorem 4.31 and equation (4.32), under the explicit uniform-majorant input.**

If the formal derivatives of the lattice-animal summands admit a summable uniform majorant on an
open neighbourhood of `[0,1]`, and the original series is summable at `p = 0`, then the animal
expansion is continuously differentiable on `[0,1]`. Its derivative at every point is exactly the
term-by-term series in (4.32).

The majorant is an explicit hypothesis rather than an axiom. It is the analytic interface supplied
in Grimmett's proof by Theorem 4.20 in the interior and the endpoint estimates (4.36)–(4.37). -/
theorem clusterDensitySeries_contDiffOn_unitInterval
    (a : ℕ → ℕ → ℕ → ℕ) {ε : ℝ} (hε : 0 < ε)
    (u : AnimalSeriesIndex → ℝ) (hu : Summable u)
    (hbound : ∀ i p, p ∈ Ioo (-ε) (1 + ε) →
      ‖animalSeriesTermDerivative a i p‖ ≤ u i)
    (hsum : Summable fun i : AnimalSeriesIndex => animalSeriesTerm a i 0) :
    ContDiffOn ℝ 1 (clusterDensitySeries a) (Icc 0 1) ∧
      ∀ p ∈ Icc (0 : ℝ) 1,
        HasDerivAt (clusterDensitySeries a) (clusterDensityDerivativeSeries a p) p := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hhas : ∀ p ∈ Ioo (-ε) (1 + ε),
      HasDerivAt (clusterDensitySeries a) (clusterDensityDerivativeSeries a p) p := by
    intro p hp
    exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
      (fun i y _hy => animalSeriesTerm_hasDerivAt a i y) hbound hzero hsum hp
  have hderivContinuous : ContinuousOn (clusterDensityDerivativeSeries a)
      (Ioo (-ε) (1 + ε)) := by
    exact continuousOn_tsum
      (fun i => (animalSeriesTermDerivative_continuous a i).continuousOn) hu hbound
  have hopen : ContDiffOn ℝ 1 (clusterDensitySeries a) (Ioo (-ε) (1 + ε)) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioo _ _)).2
    constructor
    · intro p hp
      exact (hhas p hp).differentiableAt.differentiableWithinAt
    · exact hderivContinuous.congr fun p hp =>
        (hhas p hp).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ioo _ _) p hp)
  have hsubset : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro p hp
    constructor <;> linarith [hp.1, hp.2]
  exact ⟨hopen.mono hsubset, fun p hp => hhas p (hsubset hp)⟩

end

end Percolation
