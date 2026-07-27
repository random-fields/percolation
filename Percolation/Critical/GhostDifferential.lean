import Percolation.Critical.TorusGhostAugmented
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

/-- Grimmett Lemma 5.53, equation (5.54), in infinite volume. -/
theorem ghostTheta_le_differential
    (d : ℕ) (p γ : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    ghostTheta d p γ ≤
      (γ : ℝ) * deriv (ghostThetaSeries d p) γ +
        ghostTheta d p γ ^ 2 +
          (p : ℝ) * ghostTheta d p γ *
            deriv (ghostThetaPSeries d γ) p := by
  have hleft : Tendsto (fun N : ℕ ↦
      torusGhostTheta d (N + 2) p γ) atTop
      (nhds (ghostTheta d p γ)) :=
    torusGhostTheta_tendsto d p γ hγ0
  have hright : Tendsto (fun N : ℕ ↦
      (γ : ℝ) * torusGhostThetaGammaDerivative d (N + 2) (by omega) p γ +
        torusGhostTheta d (N + 2) p γ ^ 2 +
          (p : ℝ) * torusGhostTheta d (N + 2) p γ *
            torusGhostThetaPDerivative d (N + 2) (by omega) p γ) atTop
      (nhds ((γ : ℝ) * deriv (ghostThetaSeries d p) γ +
        ghostTheta d p γ ^ 2 +
          (p : ℝ) * ghostTheta d p γ *
            deriv (ghostThetaPSeries d γ) p)) := by
    have htheta := torusGhostTheta_tendsto d p γ hγ0
    have hgamma := torusGhostTheta_gammaDeriv_tendsto d p γ hγ0 hγ1
    have hpderiv := torusGhostTheta_pDeriv_tendsto d p γ hp0 hp1 hγ0 hγ1
    exact ((tendsto_const_nhds.mul hgamma).add (htheta.pow 2)).add
      ((tendsto_const_nhds.mul htheta).mul hpderiv)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards with N
  have hfinite := torusGhostTheta_le_differential
    d (N + 2) (by omega) p γ hp1 hγ0 hγ1
  rw [← torusGhostTheta_eq_polynomial d (N + 2) (by omega) p γ] at hfinite
  exact hfinite

end

end Percolation
