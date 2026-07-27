import Percolation.Critical.AdaptiveDecisionRealization

/-!
# Antitone exhaustion for adaptive target events

This is the measure-theoretic limit step needed after the finite Bellman comparisons in Grimmett
Lemma 7.24.  Uniform lower bounds for a decreasing sequence of measurable finite-target events
pass to their intersection, and then to any limiting event containing that intersection.
-/

namespace Percolation

open MeasureTheory Filter

/-- Uniform lower bounds survive an antitone measurable exhaustion.  The conclusion event need
not itself be measurable; finiteness of the ambient measure suffices for monotonicity of its real
measure. -/
theorem measureReal_limitEvent_ge_of_antitone_exhaustion
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (A : ℕ → Set Omega) (B : Set Omega) (c : ℝ)
    (hA : ∀ n, MeasurableSet (A n))
    (hanti : Antitone A)
    (hsub : (⋂ n, A n) ⊆ B)
    (hlower : ∀ n, c ≤ mu.real (A n)) :
    c ≤ mu.real B := by
  have hmu : Tendsto (fun n : ℕ ↦ mu (A n)) atTop
      (nhds (mu (⋂ n, A n))) :=
    tendsto_measure_iInter_atTop
      (fun n ↦ (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hreal : Tendsto (fun n : ℕ ↦ mu.real (A n)) atTop
      (nhds (mu.real (⋂ n, A n))) := by
    simpa [measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmu
  have hinter : c ≤ mu.real (⋂ n, A n) :=
    ge_of_tendsto hreal (Eventually.of_forall hlower)
  exact hinter.trans (measureReal_mono hsub)

end Percolation
