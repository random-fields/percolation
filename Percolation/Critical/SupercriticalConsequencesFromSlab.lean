import Percolation.Critical.SupercriticalUniformTail
import Percolation.Critical.InfiniteClusterEdgeStrongLaw

/-!
# Chapter 8 conclusions from the Chapter 7 slab approximation

This file packages the downstream uses of Theorem 8.21.  Every premise other than
`SlabCriticalApproximation` is discharged here; that named proposition is precisely the still
unfinished unconditional output of Chapter 7 Theorem 7.2.
-/

namespace Percolation

open Filter MeasureTheory Set Topology
open scoped unitInterval

/-- Equation (8.64), with the positive radius exponent supplied by slab approximation. -/
theorem finiteClusterSizeTail_le_exp_neg_rpow_of_critical_lt_of_slabCriticalApproximation
    {d : ℕ} (hd : 3 ≤ d) (happrox : SlabCriticalApproximation d)
    (p : I) (hp : cubicCriticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ n : ℕ,
      finiteClusterSizeTail d p n ≤
        Real.exp (-eta * (n : ℝ) ^ ((d : ℝ)⁻¹)) := by
  have hp0 : 0 < (p : ℝ) :=
    (cubicCriticalProbability_pos_lt_one (by omega : 2 ≤ d)).1.trans hp
  have hrate :=
    finiteClusterRadiusDecayRate_pos_of_critical_lt_of_slabCriticalApproximation
      hd happrox p hp hp1
  exact finiteClusterSizeTail_le_exp_neg_rpow_of_radiusRate_pos
    (by omega) p hp0 hp1 hp hrate

/-- Interior source interval form of Theorem 8.92, conditional only on Chapter 7 slab
approximation.  The animal-series functions agree pointwise with `theta`, finite susceptibility,
and cluster density on the physical interval. -/
theorem theta_finiteSusceptibility_clusterDensity_contDiffOn_supercriticalInterior_of_slabCriticalApproximation
    {d : ℕ} (hd : 3 ≤ d) (happrox : SlabCriticalApproximation d) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (thetaAnimalSeries d)
        (Set.Ioo (cubicCriticalProbability d) 1) ∧
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteSusceptibilitySeries d) (Set.Ioo (cubicCriticalProbability d) 1) ∧
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (concreteClusterDensitySeries d) (Set.Ioo (cubicCriticalProbability d) 1) := by
  let pc := cubicCriticalProbability d
  have hpc0 : 0 < pc := by
    simpa [pc] using (cubicCriticalProbability_pos_lt_one (by omega : 2 ≤ d)).1
  have localAt : ∀ x : ℝ, x ∈ Set.Ioo pc 1 →
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (thetaAnimalSeries d) x ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (concreteSusceptibilitySeries d) x ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (concreteClusterDensitySeries d) x := by
    intro x hx
    have hpcx : pc < x := hx.1
    have hx1 : x < 1 := hx.2
    let a := (pc + x) / 2
    let b := (x + 1) / 2
    have hpca : pc < a := by dsimp [a]; linarith
    have hax : a < x := by dsimp [a]; linarith
    have hxb : x < b := by dsimp [b]; linarith
    have hb1 : b < 1 := by dsimp [b]; linarith
    obtain ⟨hTheta, hChi, hKappa⟩ :=
      theta_finiteSusceptibility_clusterDensity_contDiffOn_interior_of_slabCriticalApproximation
        hd happrox (by simpa [pc] using hpca) (hax.trans hxb) hb1
    have hxIoo : x ∈ Set.Ioo a b := ⟨hax, hxb⟩
    have hnhds : Set.Ioo a b ∈ 𝓝 x := Ioo_mem_nhds hax hxb
    exact ⟨(hTheta x hxIoo).contDiffAt hnhds,
      (hChi x hxIoo).contDiffAt hnhds,
      (hKappa x hxIoo).contDiffAt hnhds⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (localAt x (by simpa [pc] using hx)).1.contDiffWithinAt
  · intro x hx
    exact (localAt x (by simpa [pc] using hx)).2.1.contDiffWithinAt
  · intro x hx
    exact (localAt x (by simpa [pc] using hx)).2.2.contDiffWithinAt

/-- **Grimmett Theorem 8.99**, with its positive radius exponent supplied by slab
approximation. -/
theorem infiniteClusterBoundaryInteriorEdgeRatio_tendsto_ae_of_critical_lt_of_slabCriticalApproximation
    {d : ℕ} (hd : 3 ≤ d) (happrox : SlabCriticalApproximation d)
    (p : I) (hp : cubicCriticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ infiniteClusterBoundaryInteriorEdgeRatio d n omega)
        atTop (nhds ((1 - (p : ℝ)) / (p : ℝ))) := by
  have hp0 : 0 < (p : ℝ) :=
    (cubicCriticalProbability_pos_lt_one (by omega : 2 ≤ d)).1.trans hp
  have htheta : 0 < theta d p := theta_pos_of_criticalProbability_lt hp
  have hrate :=
    finiteClusterRadiusDecayRate_pos_of_critical_lt_of_slabCriticalApproximation
      hd happrox p hp hp1
  exact infiniteClusterBoundaryInteriorEdgeRatio_tendsto_ae_of_radiusRate_pos
    (by omega) p hp0 hp1 htheta hrate

end Percolation
