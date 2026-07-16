import Percolation.Planar.External

/-!
# Exact half-density crossing probability

This file transfers the externally cited finite planar-duality trace count to the Bernoulli
measure, proves Grimmett's Lemma 11.21, and feeds it into the exponential-decay contradiction.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

private theorem finiteBernoulliWeight_half_of_subset {ι : Type*} {E s : Finset ι}
    (hs : s ⊆ E) :
    finiteBernoulliWeight E (1 / 2) s = (1 / 2 : ℝ) ^ E.card := by
  rw [finiteBernoulliWeight, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← pow_add]
  congr 1
  exact Nat.add_sub_of_le (Finset.card_le_card hs)

private theorem finiteBernoulliProbability_eq_traceCard_mul_halfPow
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (T : Set (Finset ι))
    [DecidablePred fun s ↦ s ∈ T] :
    finiteBernoulliProbability E (1 / 2) T =
      ((E.powerset.filter fun s ↦ s ∈ T).card : ℝ) * (1 / 2 : ℝ) ^ E.card := by
  classical
  rw [finiteBernoulliProbability_eq_sum_indicator]
  calc
    (∑ s ∈ E.powerset,
        finiteBernoulliWeight E (1 / 2) s * T.indicator (fun _ ↦ 1) s) =
        ∑ s ∈ E.powerset.filter (fun s ↦ s ∈ T),
          finiteBernoulliWeight E (1 / 2) s := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases hsT : s ∈ T <;> simp [hsT]
    _ = ∑ _s ∈ E.powerset.filter (fun s ↦ s ∈ T), (1 / 2 : ℝ) ^ E.card := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [finiteBernoulliWeight_half_of_subset]
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    _ = ((E.powerset.filter fun s ↦ s ∈ T).card : ℝ) * (1 / 2 : ℝ) ^ E.card := by
      simp

private theorem finiteBernoulliProbability_add_compl
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (p : ℝ) (T : Set (Finset ι)) :
    finiteBernoulliProbability E p T + finiteBernoulliProbability E p Tᶜ = 1 := by
  classical
  calc
    finiteBernoulliProbability E p T + finiteBernoulliProbability E p Tᶜ =
        ∑ s ∈ E.powerset, finiteBernoulliWeight E p s *
          (T.indicator (fun _ ↦ 1) s + Tᶜ.indicator (fun _ ↦ 1) s) := by
      unfold finiteBernoulliProbability finiteBernoulliExpectation
      simp only [mul_add, Finset.sum_add_distrib]
    _ = ∑ s ∈ E.powerset, finiteBernoulliWeight E p s := by
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases hsT : s ∈ T <;> simp [hsT]
    _ = 1 := sum_finiteBernoulliWeight E p

private theorem finiteBernoulliWeight_dualTrace
    (n : ℕ) (p : ℝ) (s : {s // s ∈ grimmettRectangleCrossingTraces n}) :
    finiteBernoulliWeight (grimmettRectangleEdges n) p
        (grimmettRectangleDualTraceEquiv n s).1 =
      finiteBernoulliWeight (grimmettRectangleEdges n) (1 - p) s.1 := by
  classical
  have hsSubset : s.1 ⊆ grimmettRectangleEdges n := by
    exact Finset.mem_powerset.mp
      (Finset.mem_filter.mp s.2).1
  rw [finiteBernoulliWeight, finiteBernoulliWeight,
    card_grimmettRectangleDualTraceEquiv_apply]
  rw [Nat.sub_sub_self (Finset.card_le_card hsSubset)]
  ring

/-- Grimmett, Equation 11.20: the crossing probabilities at complementary bond densities sum
to one. -/
theorem grimmettRectangleCrossingProbability_add_complement (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (grimmettRectangleCrossingEvent n) +
      (bernoulliBondMeasure 2 (σ p)).real (grimmettRectangleCrossingEvent n) = 1 := by
  classical
  let E := grimmettRectangleEdges n
  let T := eventTrace (grimmettRectangleCrossingEvent n)
  have hp := DependsOn.bernoulliBondMeasure_real_eq_finiteBernoulliProbability
    (dependsOn_grimmettRectangleCrossingEvent n) p
  have hσp := DependsOn.bernoulliBondMeasure_real_eq_finiteBernoulliProbability
    (dependsOn_grimmettRectangleCrossingEvent n) (σ p)
  have hnoncross : finiteBernoulliProbability E (p : ℝ) Tᶜ =
      finiteBernoulliProbability E (1 - (p : ℝ)) T := by
    rw [finiteBernoulliProbability_eq_sum_filter,
      finiteBernoulliProbability_eq_sum_filter]
    have hfilterNon : E.powerset.filter (fun s ↦ s ∈ Tᶜ) =
        grimmettRectangleNoncrossingTraces n := by
      ext s
      simp [E, T, grimmettRectangleNoncrossingTraces]
    have hfilterCross : E.powerset.filter (fun s ↦ s ∈ T) =
        grimmettRectangleCrossingTraces n := by
      ext s
      simp [E, T, grimmettRectangleCrossingTraces]
    rw [hfilterNon, hfilterCross]
    calc
      (∑ s ∈ grimmettRectangleNoncrossingTraces n,
          finiteBernoulliWeight E (p : ℝ) s) =
          ∑ s : {s // s ∈ grimmettRectangleNoncrossingTraces n},
            finiteBernoulliWeight E (p : ℝ) s.1 := by
        rw [← Finset.attach_eq_univ, Finset.sum_attach]
      _ = ∑ s : {s // s ∈ grimmettRectangleCrossingTraces n},
          finiteBernoulliWeight E (p : ℝ)
            (grimmettRectangleDualTraceEquiv n s).1 := by
        exact ((grimmettRectangleDualTraceEquiv n).sum_comp fun s ↦
          finiteBernoulliWeight E (p : ℝ) s.1).symm
      _ = ∑ s : {s // s ∈ grimmettRectangleCrossingTraces n},
          finiteBernoulliWeight E (1 - (p : ℝ)) s.1 := by
        apply Finset.sum_congr rfl
        intro s _hs
        exact finiteBernoulliWeight_dualTrace n (p : ℝ) s
      _ = ∑ s ∈ grimmettRectangleCrossingTraces n,
          finiteBernoulliWeight E (1 - (p : ℝ)) s := by
        rw [← Finset.attach_eq_univ, Finset.sum_attach]
  have hadd := finiteBernoulliProbability_add_compl E (p : ℝ) T
  rw [hp, hσp]
  have hσ : ((σ p : I) : ℝ) = 1 - (p : ℝ) := by simp
  rw [hσ, ← hnoncross]
  linarith

/-- Grimmett, Lemma 11.21: the probability of an open left-right crossing of
`[0,n+1] × [0,n]` at density `1/2` is exactly `1/2`. -/
theorem bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half (n : ℕ) :
    (bernoulliBondMeasure 2 squareHalfDensity).real
        (grimmettRectangleCrossingEvent n) = 1 / 2 := by
  classical
  let E := grimmettRectangleEdges n
  let T := eventTrace (grimmettRectangleCrossingEvent n)
  have hambient := DependsOn.bernoulliBondMeasure_real_eq_finiteBernoulliProbability
    (dependsOn_grimmettRectangleCrossingEvent n) squareHalfDensity
  have hcross : finiteBernoulliProbability E (1 / 2) T =
      ((grimmettRectangleCrossingTraces n).card : ℝ) * (1 / 2 : ℝ) ^ E.card := by
    simpa [E, T, grimmettRectangleCrossingTraces] using
      finiteBernoulliProbability_eq_traceCard_mul_halfPow E T
  have hnoncross : finiteBernoulliProbability E (1 / 2) Tᶜ =
      ((grimmettRectangleNoncrossingTraces n).card : ℝ) * (1 / 2 : ℝ) ^ E.card := by
    simpa [E, T, grimmettRectangleNoncrossingTraces] using
      finiteBernoulliProbability_eq_traceCard_mul_halfPow E Tᶜ
  have heq : finiteBernoulliProbability E (1 / 2) T =
      finiteBernoulliProbability E (1 / 2) Tᶜ := by
    rw [hcross, hnoncross, card_grimmettRectangleCrossingTraces_eq_noncrossing]
  have hadd := finiteBernoulliProbability_add_compl E (1 / 2) T
  have hfinite : finiteBernoulliProbability E (1 / 2) T = 1 / 2 := by
    linarith
  simpa [E, T, coe_squareHalfDensity] using hambient.trans hfinite

/-- The finite planar-duality crossing lemma implies the upper bound in Grimmett,
Theorem 11.11. -/
theorem cubicCriticalProbability_two_le_half :
    cubicCriticalProbability 2 ≤ 1 / 2 := by
  apply cubicCriticalProbability_two_le_half_of_crossingProbability
  intro n
  rw [bernoulliBondMeasure_real_grimmettRectangleCrossingEvent_half]

end Percolation
