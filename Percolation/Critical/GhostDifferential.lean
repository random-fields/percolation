import Percolation.Critical.TorusGhostConditioning
import Percolation.Critical.AppendixLimits

/-!
# Infinite-volume ghost-field differential inequalities

Finite-volume inequalities are transferred to the cubic lattice using the three Appendix I
limits (5.64)--(5.66).
-/

namespace Percolation

open Set Filter
open scoped unitInterval Topology

noncomputable section

/-- Grimmett Lemma 5.51, equation (5.52), in infinite volume. -/
theorem ghostTheta_p_deriv_le
    (d : ℕ) (p γ : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    (1 - (p : ℝ)) * deriv (ghostThetaPSeries d γ) p ≤
      (2 * d : ℕ) * (1 - (γ : ℝ)) * ghostTheta d p γ *
        deriv (ghostThetaSeries d p) γ := by
  have hleft : Tendsto (fun N : ℕ ↦
      (1 - (p : ℝ)) *
        torusGhostThetaPDerivative d (N + 2) (by omega) p γ) atTop
      (nhds ((1 - (p : ℝ)) * deriv (ghostThetaPSeries d γ) p)) :=
    tendsto_const_nhds.mul
      (torusGhostTheta_pDeriv_tendsto d p γ hp0 hp1 hγ0 hγ1)
  have hright : Tendsto (fun N : ℕ ↦
      (2 * d : ℕ) * (1 - (γ : ℝ)) * torusGhostTheta d (N + 2) p γ *
        torusGhostThetaGammaDerivative d (N + 2) (by omega) p γ) atTop
      (nhds ((2 * d : ℕ) * (1 - (γ : ℝ)) * ghostTheta d p γ *
        deriv (ghostThetaSeries d p) γ)) := by
    exact (((tendsto_const_nhds.mul (torusGhostTheta_tendsto d p γ hγ0))).mul
      (torusGhostTheta_gammaDeriv_tendsto d p γ hγ0 hγ1))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards with N
  have hfinite := torusGhostTheta_p_deriv_le
    d (N + 2) (by omega) p γ hγ0 hγ1
  rw [← torusGhostTheta_eq_polynomial d (N + 2) (by omega) p γ] at hfinite
  exact hfinite

end

end Percolation
