import Percolation.Bernoulli.SequentialDominationCountable
import Percolation.Critical.DynamicRenormalization

/-!
# Probability law of a deterministic site exploration

The dynamic-renormalization state machine is deterministic once a complete Boolean answer field
is supplied.  This file proves that its finite-time states and limiting occupied set are
measurable functions of a site configuration.  Consequently the exploration output has a
well-defined pushforward probability law; this closes a concrete gap identified in the first
independent Chapter 7 review.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

variable {V : Type*} [Countable V] [DecidableEq V] [LinearOrder V]

noncomputable instance : Countable (SiteExplorationState V) := by
  let code : SiteExplorationState V →
      Finset V × Finset V × Finset V × List (V × Bool) := fun s ↦
    (s.occupied, s.rejected, s.frontier, s.history)
  have hcode : Function.Injective code := by
    intro s t h
    cases s
    cases t
    simp only [code, Prod.mk.injEq] at h
    simp_all
  exact hcode.countable

/-- Interpret a site configuration as the Boolean answer field consumed by the exploration. -/
noncomputable def configurationAnswer (η : Set V) (v : V) : Bool :=
  @decide (v ∈ η) (Classical.propDecidable _)

omit [Countable V] [DecidableEq V] [LinearOrder V] in
@[simp]
theorem configurationAnswer_eq_true_iff (η : Set V) (v : V) :
    configurationAnswer η v = true ↔ v ∈ η := by
  simp [configurationAnswer]

omit [Countable V] [DecidableEq V] [LinearOrder V] in
@[simp]
theorem configurationAnswer_eq_false_iff (η : Set V) (v : V) :
    configurationAnswer η v = false ↔ v ∉ η := by
  simp [configurationAnswer]

namespace SiteExploration

omit [Countable V] in
/-- For a fixed input state, every output-state fiber of one exploration step is measurable. -/
theorem measurableSet_step_configurationAnswer_fiber (E : SiteExploration V)
    (s t : SiteExplorationState V) :
    MeasurableSet {η : Set V | E.step (configurationAnswer η) s = t} := by
  classical
  unfold step
  split
  · by_cases hst : s = t
    · simp [hst]
    · simp [hst]
  next v hnext =>
    let accepted : SiteExplorationState V :=
      { occupied := insert v s.occupied
        rejected := s.rejected
        frontier :=
          (s.frontier.erase v ∪ E.neighbors v) \ (insert v s.occupied ∪ s.rejected)
        history := s.history ++ [(v, true)] }
    let rejected : SiteExplorationState V :=
      { occupied := s.occupied
        rejected := insert v s.rejected
        frontier := s.frontier.erase v
        history := s.history ++ [(v, false)] }
    change MeasurableSet
      {η : Set V | (if configurationAnswer η v then accepted else rejected) = t}
    by_cases ha : accepted = t <;> by_cases hr : rejected = t
    · have hEvent : {η : Set V |
          (if configurationAnswer η v then accepted else rejected) = t} = Set.univ := by
        ext η
        simp [ha, hr]
      rw [hEvent]
      exact MeasurableSet.univ
    · have hEvent : {η : Set V |
          (if configurationAnswer η v then accepted else rejected) = t} = {η | v ∈ η} := by
        ext η
        by_cases hv : v ∈ η <;> simp [configurationAnswer, hv, ha, hr]
      rw [hEvent]
      exact measurableSet_mem v
    · have hEvent : {η : Set V |
          (if configurationAnswer η v then accepted else rejected) = t} = {η | v ∉ η} := by
        ext η
        by_cases hv : v ∈ η <;> simp [configurationAnswer, hv, ha, hr]
      rw [hEvent]
      exact (measurableSet_mem v).compl
    · have hEvent : {η : Set V |
          (if configurationAnswer η v then accepted else rejected) = t} = ∅ := by
        ext η
        by_cases hv : v ∈ η <;> simp [configurationAnswer, hv, ha, hr]
      rw [hEvent]
      exact MeasurableSet.empty

/-- Every exact finite-time exploration-state history is a measurable event. -/
theorem measurableSet_stateAfter_configurationAnswer_fiber (E : SiteExploration V) :
    ∀ n (t : SiteExplorationState V),
      MeasurableSet {η : Set V | E.stateAfter (configurationAnswer η) n = t} := by
  intro n
  induction n with
  | zero =>
      intro t
      by_cases h : E.initial = t
      · simp [stateAfter, h]
      · simp [stateAfter, h]
  | succ n ih =>
      intro t
      have hrepr : {η : Set V | E.stateAfter (configurationAnswer η) (n + 1) = t} =
          ⋃ s : SiteExplorationState V,
            {η | E.stateAfter (configurationAnswer η) n = s} ∩
              {η | E.step (configurationAnswer η) s = t} := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, stateAfter]
        constructor
        · intro h
          exact ⟨E.stateAfter (configurationAnswer η) n, rfl, h⟩
        · rintro ⟨s, hs, hst⟩
          simpa [hs] using hst
      rw [hrepr]
      exact MeasurableSet.iUnion fun s ↦
        (ih s).inter (E.measurableSet_step_configurationAnswer_fiber s t)

/-- Membership of a vertex in the limiting accepted set is measurable. -/
theorem measurableSet_mem_occupiedLimit_configurationAnswer (E : SiteExploration V) (v : V) :
    MeasurableSet {η : Set V | v ∈ E.occupiedLimit (configurationAnswer η)} := by
  have hrepr : {η : Set V | v ∈ E.occupiedLimit (configurationAnswer η)} =
      ⋃ n : ℕ, ⋃ s : SiteExplorationState V,
        if v ∈ s.occupied then
          {η | E.stateAfter (configurationAnswer η) n = s}
        else ∅ := by
    ext η
    simp only [occupiedLimit, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n, hv⟩
      refine ⟨n, E.stateAfter (configurationAnswer η) n, ?_⟩
      rw [if_pos hv]
      rfl
    · rintro ⟨n, s, hs⟩
      split at hs
      next hv =>
        exact ⟨n, hs ▸ hv⟩
      next => simp at hs
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro s
  split
  · exact E.measurableSet_stateAfter_configurationAnswer_fiber n s
  · exact MeasurableSet.empty

/-- The limiting occupied-set map is measurable into the canonical product measurable space on
site configurations. -/
theorem measurable_occupiedLimit_configurationAnswer (E : SiteExploration V) :
    Measurable fun η : Set V ↦ E.occupiedLimit (configurationAnswer η) := by
  change Measurable
    ((fun P : V → Prop ↦ {v | P v}) ∘
      fun (η : Set V) (v : V) ↦ (v ∈ E.occupiedLimit (configurationAnswer η) : Prop))
  refine Measurable.comp (by fun_prop) ?_
  exact measurable_pi_lambda _ fun v ↦
    (E.measurableSet_mem_occupiedLimit_configurationAnswer v).mem

/-- Pushforward probability law of the limiting accepted set `A∞`. -/
noncomputable def occupiedLimitLaw (E : SiteExploration V)
    (μ : Measure (Set V)) : Measure (Set V) :=
  μ.map fun η ↦ E.occupiedLimit (configurationAnswer η)

instance occupiedLimitLaw_isProbabilityMeasure (E : SiteExploration V)
    (μ : Measure (Set V)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (E.occupiedLimitLaw μ) :=
  Measure.isProbabilityMeasure_map E.measurable_occupiedLimit_configurationAnswer.aemeasurable

/-- Prefix-history hypothesis for the actual pushforward law of `A∞`. -/
def OccupiedLimitHasPrefixLowerBound (E : SiteExploration V) (μ : Measure (Set V))
    (e : ℕ ≃ V) (p : ℝ) : Prop :=
  ∀ n, HasFiniteSequentialLowerBound (enumerationPrefixLaw e n (E.occupiedLimitLaw μ)) p

/-- Once the exact prefix inequalities have been derived from the exploration histories, the
limiting accepted set is infinite with positive probability (indeed, with probability one under
this stronger output-law hypothesis). -/
theorem occupiedLimit_infinite_probability_pos_of_prefixLowerBound
    (E : SiteExploration V) (μ : Measure (Set V)) [IsProbabilityMeasure μ]
    (e : ℕ ≃ V) (p : I) (hp : 0 < (p : ℝ))
    (hseq : E.OccupiedLimitHasPrefixLowerBound μ e (p : ℝ)) :
    0 < μ.real {η : Set V | (E.occupiedLimit (configurationAnswer η)).Infinite} := by
  have houtEq := infinite_siteSet_probability_eq_one_of_prefixSequential e
    (E.occupiedLimitLaw μ) p hp hseq
  have hout : 0 < (E.occupiedLimitLaw μ).real {ξ : Set V | ξ.Infinite} := by
    rw [houtEq]
    norm_num
  have hInf : MeasurableSet {ξ : Set V | ξ.Infinite} := MeasurableSet.setOf_infinite
  rw [occupiedLimitLaw, map_measureReal_apply
    E.measurable_occupiedLimit_configurationAnswer hInf] at hout
  exact hout

/-- Strengthened exploration conclusion: under the accepted-site rooted invariant, an infinite
output is not merely an infinite set but an infinite site-open cluster of the exploration graph.
This closes the semantic gap between cardinality and connectivity in Lemma 7.24. -/
theorem occupiedLimit_hasInfiniteSiteCluster_probability_pos_of_prefixLowerBound
    (E : SiteExploration V) (μ : Measure (Set V)) [IsProbabilityMeasure μ]
    (e : ℕ ≃ V) (p : I) (hp : 0 < (p : ℝ)) (root : V)
    (hinitial : E.OpenRootedAt root E.initial)
    (hseq : E.OccupiedLimitHasPrefixLowerBound μ e (p : ℝ)) :
    0 < μ.real {η : Set V |
      hasInfiniteSiteCluster E.graph (E.occupiedLimit (configurationAnswer η))} := by
  have hInf := E.occupiedLimit_infinite_probability_pos_of_prefixLowerBound μ e p hp hseq
  exact hInf.trans_le <| measureReal_mono fun η hη ↦
    E.hasInfiniteSiteCluster_occupiedLimit_of_infinite
      (configurationAnswer η) root hinitial hη

end SiteExploration

end Percolation
