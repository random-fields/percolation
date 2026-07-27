import Percolation.Critical.AdaptiveAnswerSupport
import Percolation.Bernoulli.FKGInfinite

/-!
# Finite coordinate supports for set-valued adaptive answers

The existing adaptive-support API is phrased for real coordinate fields.  Boundary-edge
explorations instead read an iid Bernoulli subset.  This file supplies the corresponding
finite-support and fresh-block factorization theorem for `Set ι` configurations.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical
open scoped unitInterval

/-- A Bernoulli subset hits a fixed finite coordinate block with probability
`1 - (1-p)^|S|`. -/
theorem setBernoulli_real_not_disjoint_finset_univ
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : I) :
    setBer((Set.univ : Set ι), p).real
        {omega : Set ι | ¬ Disjoint (S : Set ι) omega} =
      1 - (1 - (p : ℝ)) ^ S.card := by
  let A := {omega : Set ι | Disjoint (S : Set ι) omega}
  have hA : MeasurableSet A := by
    classical
    rw [show A = ⋂ x ∈ S, {omega : Set ι | x ∉ omega} by
      ext omega
      simp [A, Set.disjoint_left]]
    exact S.measurableSet_biInter fun x _ ↦ (measurableSet_mem x).compl
  have hcompl : {omega : Set ι | ¬ Disjoint (S : Set ι) omega} = Aᶜ := by
    ext omega
    rfl
  rw [hcompl, measureReal_compl hA, probReal_univ,
    setBernoulli_real_disjoint_finset_univ]

namespace AdaptiveSiteExploration

variable {Q ι : Type*} [DecidableEq ι]

/-- Every Boolean answer fiber depends only on its advertised finite coordinate block. -/
def HasFiniteSetAnswerSupports
    (answer : Set ι → List (Q × Bool) → Q → Bool)
    (support : List (Q × Bool) → Q → Finset ι) : Prop :=
  ∀ history q b, DependsOn (support history q)
    {omega : Set ι | answer omega history q = b}

omit [DecidableEq ι] in
theorem HasFiniteSetAnswerSupports.measurableAnswer
    {answer : Set ι → List (Q × Bool) → Q → Bool}
    {support : List (Q × Bool) → Q → Finset ι}
    (h : HasFiniteSetAnswerSupports answer support) : MeasurableAnswer answer := by
  intro history q
  apply measurable_to_bool
  exact (h history q true).measurableSet

/-- An exact adaptive answer history depends on the union of the blocks read along it. -/
theorem dependsOn_adaptiveAnswerHistoryEventFrom_setSupports
    {answer : Set ι → List (Q × Bool) → Q → Bool}
    {support : List (Q × Bool) → Q → Finset ι}
    (h : HasFiniteSetAnswerSupports answer support) :
    ∀ prior suffix,
      DependsOn (adaptiveAnswerHistorySupportFrom support prior suffix)
        (adaptiveAnswerHistoryEventFrom answer prior suffix) := by
  intro prior suffix
  induction suffix generalizing prior with
  | nil => simpa using dependsOn_univ (∅ : Finset ι)
  | cons head suffix ih =>
      rcases head with ⟨q, b⟩
      simp only [adaptiveAnswerHistoryEventFrom, adaptiveAnswerHistorySupportFrom]
      exact
        ((h prior q b).mono Finset.subset_union_left).inter
          ((ih (prior ++ [(q, b)])).mono Finset.subset_union_right)

theorem dependsOn_adaptiveAnswerHistoryEvent_setSupports
    {answer : Set ι → List (Q × Bool) → Q → Bool}
    {support : List (Q × Bool) → Q → Finset ι}
    (h : HasFiniteSetAnswerSupports answer support)
    (history : List (Q × Bool)) :
    DependsOn (adaptiveAnswerHistorySupport support history)
      (adaptiveAnswerHistoryEvent answer history) := by
  exact dependsOn_adaptiveAnswerHistoryEventFrom_setSupports h [] history

/-- A fresh Bernoulli block gives a history-wise upper kernel bound.  The conclusion is in
ratio-free intersection form and therefore remains meaningful when the history has probability
zero. -/
theorem hasAdaptiveAnswerUpperBoundOn_setBernoulli_of_fresh_support
    (p : I)
    {answer : Set ι → List (Q × Bool) → Q → Bool}
    {support : List (Q × Bool) → Q → Finset ι}
    (hsupport : HasFiniteSetAnswerSupports answer support)
    (admissible : List (Q × Bool) → Q → Prop)
    (q : ℝ)
    (hfresh : ∀ history x, admissible history x →
      Disjoint (adaptiveAnswerHistorySupport support history : Set ι)
        (support history x : Set ι))
    (hsingle : ∀ history x, admissible history x →
      setBer((Set.univ : Set ι), p).real
          {omega : Set ι | answer omega history x = true} ≤ q) :
    HasAdaptiveAnswerUpperBoundOn setBer((Set.univ : Set ι), p)
      answer admissible q := by
  intro history x hadmissible
  let S : Set ι := adaptiveAnswerHistorySupport support history
  let T : Set ι := support history x
  let A : Set (Set ι) := adaptiveAnswerHistoryEvent answer history
  let B : Set (Set ι) := {omega | answer omega history x = true}
  have hAdep : DependsOn (adaptiveAnswerHistorySupport support history) A :=
    dependsOn_adaptiveAnswerHistoryEvent_setSupports hsupport history
  have hBdep : DependsOn (support history x) B := hsupport history x true
  have hA : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents S)] A := by
    exact hAdep.measurableSet_generateFrom_coordinateEvents (by rfl)
  have hB : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents T)] B := by
    exact hBdep.measurableSet_generateFrom_coordinateEvents (by rfl)
  have hind : IndepSet A B setBer((Set.univ : Set ι), p) :=
    (indep_generateFrom_coordinateEvents p (hfresh history x hadmissible)
      ).indepSet_of_measurableSet hA hB
  have hfactor := congrArg ENNReal.toReal hind.measure_inter_eq_mul
  rw [ENNReal.toReal_mul] at hfactor
  have hfactorReal :
      setBer((Set.univ : Set ι), p).real (A ∩ B) =
        setBer((Set.univ : Set ι), p).real A *
          setBer((Set.univ : Set ι), p).real B := by
    simpa [measureReal_def] using hfactor
  have hextend :
      adaptiveAnswerHistoryEvent answer (history ++ [(x, true)]) = A ∩ B := by
    rw [adaptiveAnswerHistoryEvent_append_singleton]
  rw [hextend, hfactorReal]
  calc
    setBer((Set.univ : Set ι), p).real A *
          setBer((Set.univ : Set ι), p).real B ≤
        setBer((Set.univ : Set ι), p).real A * q :=
      mul_le_mul_of_nonneg_left (hsingle history x hadmissible) measureReal_nonneg
    _ = q * setBer((Set.univ : Set ι), p).real A := mul_comm _ _

end AdaptiveSiteExploration

end Percolation
