import Percolation.Critical.Regions

/-!
# Slab critical-point limit assembly

This is the order-theoretic final step of Grimmett Theorem 7.2(b).  The dynamic block
construction in part (a), applied to the coordinate plane, supplies arbitrarily accurate upper
bounds.  Region inclusion supplies the matching lower bound and slab widths are antitone.
-/

namespace Percolation

open Filter

/-- Exact approximation output needed from Theorem 7.2(a) for the slab specialization. -/
def SlabCriticalApproximation (d : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ k : ℕ,
    slabCriticalProbability d k ≤ cubicCriticalProbability d + η

/-- The final analytic step of Theorem 7.2(b): arbitrary upper approximation, together with
the already proved region-inclusion lower bound and width monotonicity, forces convergence. -/
theorem slabCriticalProbability_tendsto_cubicCriticalProbability_of_approximation
    (d : ℕ) (happrox : SlabCriticalApproximation d) :
    Filter.Tendsto (slabCriticalProbability d) Filter.atTop
      (nhds (cubicCriticalProbability d)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := happrox (ε / 2) (by positivity)
  refine ⟨k, fun n hkn ↦ ?_⟩
  have hlower := cubicCriticalProbability_le_slabCriticalProbability d n
  have hupper : slabCriticalProbability d n ≤ cubicCriticalProbability d + ε / 2 :=
    (slabCriticalProbability_antitone d hkn).trans hk
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

end Percolation
