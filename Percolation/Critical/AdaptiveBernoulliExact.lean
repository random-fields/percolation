import Percolation.Bernoulli.FKGInfinite
import Percolation.Critical.AdaptiveDecisionTree

/-!
# Exact Bernoulli laws for fresh adaptive coordinate queries

An adaptive algorithm may choose its next Bernoulli coordinate from the preceding answers.  If
the chosen coordinate has not appeared earlier in the literal history, its next answer still has
exactly the Bernoulli parameter, in the ratio-free intersection form used by the Chapter 7
decision-tree kernels.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Classical
open scoped unitInterval

namespace AdaptiveSiteExploration

variable {Q ι : Type*} [DecidableEq ι]

/-- Boolean oracle obtained by reading the Bernoulli coordinate assigned to the query. -/
noncomputable def membershipAdaptiveAnswer
    (coord : Q → ι) : Set ι → List (Q × Bool) → Q → Bool :=
  fun omega _history q ↦ decide (coord q ∈ omega)

theorem membershipAdaptiveAnswer_eq_true_iff
    (coord : Q → ι) (omega : Set ι) (history : List (Q × Bool)) (q : Q) :
    membershipAdaptiveAnswer coord omega history q = true ↔ coord q ∈ omega := by
  simp [membershipAdaptiveAnswer]

/-- Coordinates mentioned by a literal query/answer history. -/
noncomputable def adaptiveHistoryCoordinateSupport
    (coord : Q → ι) (history : List (Q × Bool)) : Finset ι :=
  history.toFinset.image (fun entry ↦ coord entry.1)

@[simp]
theorem adaptiveHistoryCoordinateSupport_nil (coord : Q → ι) :
    adaptiveHistoryCoordinateSupport coord [] = ∅ := by
  simp [adaptiveHistoryCoordinateSupport]

@[simp]
theorem adaptiveHistoryCoordinateSupport_cons
    (coord : Q → ι) (head : Q × Bool) (tail : List (Q × Bool)) :
    adaptiveHistoryCoordinateSupport coord (head :: tail) =
      insert (coord head.1) (adaptiveHistoryCoordinateSupport coord tail) := by
  simp [adaptiveHistoryCoordinateSupport]

theorem dependsOn_membershipAdaptiveAnswer_fiber
    (coord : Q → ι) (history : List (Q × Bool)) (q : Q) (b : Bool) :
    DependsOn {coord q} {omega : Set ι |
      membershipAdaptiveAnswer coord omega history q = b} := by
  intro omega eta hagree
  have hcoord : coord q ∈ omega ↔ coord q ∈ eta :=
    hagree (coord q) (by simp)
  cases b <;> simp [membershipAdaptiveAnswer, hcoord]

/-- The exact event of producing `history` reads only the coordinates occurring in that
history. -/
theorem dependsOn_adaptiveAnswerHistoryEvent_membership
    (coord : Q → ι) (history : List (Q × Bool)) :
    DependsOn (adaptiveHistoryCoordinateSupport coord history)
      (adaptiveAnswerHistoryEvent (membershipAdaptiveAnswer coord) history) := by
  rw [adaptiveAnswerHistoryEvent]
  suffices h : ∀ (prior suffix : List (Q × Bool)),
      DependsOn (adaptiveHistoryCoordinateSupport coord suffix)
        (adaptiveAnswerHistoryEventFrom (membershipAdaptiveAnswer coord) prior suffix) by
    exact h [] history
  intro prior suffix
  induction suffix generalizing prior with
  | nil =>
      simpa using dependsOn_univ (∅ : Finset ι)
  | cons head suffix ih =>
      rcases head with ⟨q, b⟩
      rw [adaptiveAnswerHistoryEventFrom, adaptiveHistoryCoordinateSupport_cons]
      apply DependsOn.inter
      · exact (dependsOn_membershipAdaptiveAnswer_fiber coord prior q b).mono
          (by simp)
      · exact (ih (prior ++ [(q, b)])).mono (by simp)

theorem measurableAnswer_membershipAdaptiveAnswer (coord : Q → ι) :
    MeasurableAnswer (membershipAdaptiveAnswer coord) := by
  intro history q
  change Measurable fun omega : Set ι ↦
    if coord q ∈ omega then true else false
  exact Measurable.ite (measurableSet_coordinateEvent (coord q))
    measurable_const measurable_const

/-- A genuinely fresh adaptive coordinate has its exact Bernoulli mass after every admitted
history. -/
theorem hasAdaptiveAnswerExactOn_membership_of_fresh
    (p : I) (coord : Q → ι)
    (admissible : List (Q × Bool) → Q → Prop)
    (hfresh : ∀ history q, admissible history q →
      coord q ∉ adaptiveHistoryCoordinateSupport coord history) :
    HasAdaptiveAnswerExactOn setBer((Set.univ : Set ι), p)
      (membershipAdaptiveAnswer coord) admissible (p : ℝ) := by
  intro history q hadmissible
  let S : Set ι := adaptiveHistoryCoordinateSupport coord history
  let T : Set ι := {coord q}
  let A : Set (Set ι) :=
    adaptiveAnswerHistoryEvent (membershipAdaptiveAnswer coord) history
  let B : Set (Set ι) := {omega | coord q ∈ omega}
  have hST : Disjoint S T := by
    rw [Set.disjoint_singleton_right]
    exact hfresh history q hadmissible
  have hA : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents S)] A := by
    apply (dependsOn_adaptiveAnswerHistoryEvent_membership coord history
      ).measurableSet_generateFrom_coordinateEvents
    exact Set.Subset.rfl
  have hB : MeasurableSet[MeasurableSpace.generateFrom (coordinateEvents T)] B := by
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨coord q, Set.mem_singleton _, rfl⟩
  have hind : IndepSet A B setBer((Set.univ : Set ι), p) :=
    (indep_generateFrom_coordinateEvents p hST).indepSet_of_measurableSet hA hB
  have hfactor := congrArg ENNReal.toReal hind.measure_inter_eq_mul
  rw [ENNReal.toReal_mul] at hfactor
  have hfactorReal :
      setBer((Set.univ : Set ι), p).real (A ∩ B) =
        setBer((Set.univ : Set ι), p).real A *
          setBer((Set.univ : Set ι), p).real B := by
    simpa [measureReal_def] using hfactor
  have hcoordinate : setBer((Set.univ : Set ι), p).real B = (p : ℝ) := by
    have hsingle := setBernoulli_real_superset_finset_univ ({coord q} : Finset ι) p
    simpa [B, Set.singleton_subset_iff] using hsingle
  have hextend :
      adaptiveAnswerHistoryEvent (membershipAdaptiveAnswer coord)
          (history ++ [(q, true)]) = A ∩ B := by
    rw [adaptiveAnswerHistoryEvent_append_singleton]
    ext omega
    simp [A, B, membershipAdaptiveAnswer]
  rw [hextend, hfactorReal, hcoordinate]
  simp [A, mul_comm]

end AdaptiveSiteExploration

end Percolation
