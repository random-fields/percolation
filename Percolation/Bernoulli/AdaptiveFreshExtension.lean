import Percolation.Bernoulli.FKGInfinite

/-!
# Adaptive finite fresh-edge extensions

After observing a finite Bernoulli trace, one may choose a fixed-size set of coordinates which
is disjoint from the observed support.  Requiring all chosen coordinates to be open costs exactly
the corresponding power of the Bernoulli parameter, even though the choice depends on the trace.
This finite trace lemma is the rigorous form of the one-fresh-edge argument after Grimmett's
Lemma 11.21.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Union of trace cells in `T`, with the trace-dependent fresh coordinate set required open. -/
noncomputable def adaptiveFreshOpenExtensionEvent
    {d : ℕ} (E : Finset (CubicEdge d)) (T : Finset (Finset (CubicEdge d)))
    (fresh : Finset (CubicEdge d) → Finset (CubicEdge d)) :
    Set (EdgeConfiguration d) := by
  classical
  exact ⋃ s ∈ T,
    finiteCylinder E s ∩ openEdgeSetEvent d (fresh s)

theorem measurableSet_adaptiveFreshOpenExtensionEvent
    {d : ℕ} (E : Finset (CubicEdge d)) (T : Finset (Finset (CubicEdge d)))
    (hT : T ⊆ E.powerset)
    (fresh : Finset (CubicEdge d) → Finset (CubicEdge d)) :
    MeasurableSet (adaptiveFreshOpenExtensionEvent E T fresh) := by
  classical
  unfold adaptiveFreshOpenExtensionEvent
  exact T.measurableSet_biUnion fun s hs ↦
    (measurableSet_finiteCylinder
      (Finset.mem_powerset.mp (hT hs))).inter
      (measurableSet_openEdgeSetEvent d (fresh s))

private theorem adaptiveFresh_cell_probability
    {d k : ℕ} (p : I) {E s : Finset (CubicEdge d)} (hs : s ⊆ E)
    (fresh : Finset (CubicEdge d)) (hfresh : Disjoint fresh E)
    (hcard : fresh.card = k) :
    (bernoulliBondMeasure d p).real
        (finiteCylinder E s ∩ openEdgeSetEvent d fresh) =
      (p : ℝ) ^ k * finiteBernoulliWeight E (p : ℝ) s := by
  classical
  have hpre :
      (fun ω : EdgeConfiguration d ↦ spliceOn E s ω) ⁻¹'
          openEdgeSetEvent d fresh = openEdgeSetEvent d fresh := by
    ext ω
    simp only [Set.mem_preimage, openEdgeSetEvent, Set.mem_setOf_eq]
    constructor
    · intro h e he
      have heE : e ∉ E := by
        intro he'
        exact Finset.disjoint_left.mp hfresh he he'
      exact (mem_spliceOn_of_notMem hs heE).mp (h he)
    · intro h e he
      have heE : e ∉ E := by
        intro he'
        exact Finset.disjoint_left.mp hfresh he he'
      exact (mem_spliceOn_of_notMem hs heE).mpr (h he)
  have hfactor := setBernoulli_real_inter_finiteCylinder
    (p := p) hs (measurableSet_openEdgeSetEvent d fresh)
  change (bernoulliBondMeasure d p).real
      (openEdgeSetEvent d fresh ∩ finiteCylinder E s) =
    (bernoulliBondMeasure d p).real
        ((fun ω : EdgeConfiguration d ↦ spliceOn E s ω) ⁻¹'
          openEdgeSetEvent d fresh) * finiteBernoulliWeight E (p : ℝ) s at hfactor
  rw [hpre, bernoulliBondMeasure_real_openEdgeSetEvent, hcard] at hfactor
  simpa [Set.inter_comm] using hfactor

/-- Exact probability of a trace-dependent fixed-cardinality fresh open extension. -/
theorem bernoulliBondMeasure_real_adaptiveFreshOpenExtensionEvent
    {d k : ℕ} (p : I) (E : Finset (CubicEdge d))
    (T : Finset (Finset (CubicEdge d))) (hT : T ⊆ E.powerset)
    (fresh : Finset (CubicEdge d) → Finset (CubicEdge d))
    (hfresh : ∀ s ∈ T, Disjoint (fresh s) E)
    (hcard : ∀ s ∈ T, (fresh s).card = k) :
    (bernoulliBondMeasure d p).real (adaptiveFreshOpenExtensionEvent E T fresh) =
      (p : ℝ) ^ k * ∑ s ∈ T, finiteBernoulliWeight E (p : ℝ) s := by
  classical
  letI : IsProbabilityMeasure (bernoulliBondMeasure d p) := by
    dsimp [bernoulliBondMeasure]
    infer_instance
  have hdisj : Set.PairwiseDisjoint (↑T : Set (Finset (CubicEdge d)))
      (fun s ↦ finiteCylinder E s ∩ openEdgeSetEvent d (fresh s)) :=
    by
      intro s hs t ht hst
      exact (pairwiseDisjoint_finiteCylinder E (hT hs) (hT ht) hst).mono
        Set.inter_subset_left Set.inter_subset_left
  rw [adaptiveFreshOpenExtensionEvent]
  rw [measureReal_biUnion_finset hdisj (fun s hs ↦
    (measurableSet_finiteCylinder (Finset.mem_powerset.mp (hT hs))).inter
      (measurableSet_openEdgeSetEvent d (fresh s)))
    (fun _s _hs ↦ measure_ne_top _ _)]
  calc
    ∑ s ∈ T,
        (bernoulliBondMeasure d p).real
          (finiteCylinder E s ∩ openEdgeSetEvent d (fresh s)) =
        ∑ s ∈ T,
          (p : ℝ) ^ k * finiteBernoulliWeight E (p : ℝ) s := by
      apply Finset.sum_congr rfl
      intro s hs
      exact adaptiveFresh_cell_probability p
        (Finset.mem_powerset.mp (hT hs))
        (fresh s) (hfresh s hs) (hcard s hs)
    _ = (p : ℝ) ^ k *
        ∑ s ∈ T,
          finiteBernoulliWeight E (p : ℝ) s := by
      rw [Finset.mul_sum]

end Percolation
