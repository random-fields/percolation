import Percolation.Critical.AdaptiveSiteExplorationTheorem
import Mathlib.Probability.ConditionalProbability

/-!
# Adaptive exploration after a positive initialization event

The root block in Grimmett's proof of Theorem 7.2 is not an ordinary queried coarse site.  The
argument first conditions on the central seed and the successful root branches, an event of
positive probability, and only then explores the neighbouring coarse sites.  This file packages
that step without dividing by a possibly null history: all hypotheses remain ratio-free
intersection inequalities under the original measure, and conditioning is performed only after
the outer event has explicitly been proved positive.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical
open scoped unitInterval

namespace AdaptiveSiteExploration

variable {Omega V : Type*}

/-- Ratio-free lower answer law inside a fixed outer initialization event.  This is the literal
form needed for the root seed/root-branch event in Theorem 7.2. -/
def HasAdaptiveAnswerLowerBoundWithin
    [MeasurableSpace Omega]
    (mu : Measure Omega) (outer : Set Omega)
    (answer : Omega → List (V × Bool) → V → Bool)
    (admissible : List (V × Bool) → V → Prop) (q : ℝ) : Prop :=
  ∀ history v, admissible history v →
    q * mu.real (outer ∩ adaptiveAnswerHistoryEvent answer history) ≤
      mu.real (outer ∩
        adaptiveAnswerHistoryEvent answer (history ++ [(v, true)]))

theorem HasAdaptiveAnswerLowerBoundWithin.mono_density
    [MeasurableSpace Omega]
    {mu : Measure Omega} {outer : Set Omega}
    {answer : Omega → List (V × Bool) → V → Bool}
    {admissible : List (V × Bool) → V → Prop} {q q' : ℝ}
    (h : HasAdaptiveAnswerLowerBoundWithin mu outer answer admissible q)
    (hq : q' ≤ q) :
    HasAdaptiveAnswerLowerBoundWithin mu outer answer admissible q' := by
  intro history v hadmissible
  exact (mul_le_mul_of_nonneg_right hq measureReal_nonneg).trans
    (h history v hadmissible)

/-- Real-valued conditional probability, written as the positive common scale times the
corresponding intersection mass.  Measurability of the conditioning event is enough; the queried
set need not be repeated as an extra hypothesis. -/
theorem measureReal_cond_apply
    [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    {outer : Set Omega} (houter : MeasurableSet outer) (event : Set Omega) :
    (mu[|outer]).real event =
      (mu.real outer)⁻¹ * mu.real (outer ∩ event) := by
  rw [Measure.real, cond_apply houter]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rfl

/-- A ratio-free law inside a positive outer event is exactly an ordinary adaptive lower law
under the conditional probability measure. -/
theorem HasAdaptiveAnswerLowerBoundWithin.cond
    [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {outer : Set Omega} (houter : MeasurableSet outer)
    {answer : Omega → List (V × Bool) → V → Bool}
    {admissible : List (V × Bool) → V → Prop} {q : ℝ}
    (h : HasAdaptiveAnswerLowerBoundWithin mu outer answer admissible q) :
    HasAdaptiveAnswerLowerBoundOn (mu[|outer]) answer admissible q := by
  intro history v hadmissible
  rw [measureReal_cond_apply mu houter,
    measureReal_cond_apply mu houter]
  calc
    q * ((mu.real outer)⁻¹ *
        mu.real (outer ∩ adaptiveAnswerHistoryEvent answer history)) =
        (mu.real outer)⁻¹ *
          (q * mu.real (outer ∩ adaptiveAnswerHistoryEvent answer history)) := by
      ring
    _ ≤ (mu.real outer)⁻¹ *
        mu.real (outer ∩
          adaptiveAnswerHistoryEvent answer (history ++ [(v, true)])) :=
      mul_le_mul_of_nonneg_left (h history v hadmissible) (inv_nonneg.mpr measureReal_nonneg)

end AdaptiveSiteExploration

namespace SiteExploration

/-- Outer-event form of Grimmett Lemma 7.24.  A positive initialization event, together with
the exact ratio-free history bounds inside that event, forces a positive original probability
of an infinite adaptive occupied set occurring together with the initialization. -/
theorem cubicRegionSiteExploration_infinite_inter_probability_pos_of_adaptiveLowerBoundWithin
    {Omega : Type*} [MeasurableSpace Omega]
    (d : ℕ) (F : Set (Cubic d)) [LinearOrder F] (root : F)
    (hF : (cubicRegionGraph d F).Connected)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (outer : Set Omega) (houter : MeasurableSet outer)
    (houterPos : 0 < mu.real outer)
    (q : I) (hq : siteCriticalProbability (cubicRegionGraph d F) < (q : ℝ))
    {answer : Omega → List (F × Bool) → F → Bool}
    (hanswer : AdaptiveSiteExploration.MeasurableAnswer answer)
    (hlower : AdaptiveSiteExploration.HasAdaptiveAnswerLowerBoundWithin mu outer
      (prefixedAdaptiveAnswer
        (cubicRegionSiteExploration d F root).initial.history answer)
      (fun _ _ ↦ True) (q : ℝ)) :
    0 < mu.real (outer ∩ {omega |
      ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
        (answer omega)).Infinite}) := by
  have houterNe : mu outer ≠ 0 := by
    intro hzero
    rw [Measure.real, hzero] at houterPos
    simp at houterPos
  letI : IsProbabilityMeasure (mu[|outer]) := cond_isProbabilityMeasure houterNe
  have hcondPos :
      0 < (mu[|outer]).real {omega |
        ((cubicRegionSiteExploration d F root).toAdaptive.occupiedLimit
          (answer omega)).Infinite} :=
    cubicRegionSiteExploration_infinite_probability_pos_of_adaptiveLowerBound
      d F root hF (mu[|outer]) q hq hanswer (hlower.cond houter)
  rw [AdaptiveSiteExploration.measureReal_cond_apply mu houter] at hcondPos
  exact pos_of_mul_pos_right hcondPos (inv_nonneg.mpr measureReal_nonneg)

end SiteExploration

end Percolation
