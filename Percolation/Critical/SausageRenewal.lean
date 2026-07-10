import Percolation.Critical.PivotalDomination
import Percolation.Critical.RenewalDomination

/-!
# From sausage domination to the pivotal-count bound

This file carries out the finite renewal comparison in Grimmett's equations
(5.18)--(5.21), culminating in Lemma 5.17.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval BigOperators Classical

/-- Total Bernoulli mass of all feasible `k`-gap extensions of a prescribed
sausage history, with `b` units of radial budget remaining. -/
noncomputable def sausageCompletionMass (d : ℕ) (p : I) (n : ℕ) :
    List ℕ → ℕ → ℕ → ℝ
  | rs, 0, _ => (bernoulliBondMeasure d p).real
      (sausageGapPrefixEvent d cubicOrigin n rs)
  | rs, k + 1, b => ∑ t ∈ Finset.range b,
      sausageCompletionMass d p n (rs ++ [t]) k (b - (t + 1))

/-- Event represented by `sausageCompletionMass`. -/
def sausageCompletionEvent (d n : ℕ) : List ℕ → ℕ → ℕ →
    Set (EdgeConfiguration d)
  | rs, 0, _ => sausageGapPrefixEvent d cubicOrigin n rs
  | rs, k + 1, b => ⋃ t ∈ Finset.range b,
      sausageCompletionEvent d n (rs ++ [t]) k (b - (t + 1))

theorem sausageCompletionEvent_subset_prefix
    {d n : ℕ} (rs : List ℕ) (k b : ℕ) :
    sausageCompletionEvent d n rs k b ⊆
      sausageGapPrefixEvent d cubicOrigin n rs := by
  induction k generalizing rs b with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
      rw [sausageCompletionEvent]
      rintro ω hω
      rw [Set.mem_iUnion₂] at hω
      obtain ⟨t, ht, hω⟩ := hω
      have hext := ih (rs ++ [t]) (b - (t + 1)) hω
      rw [sausageGapPrefixEvent_append_singleton] at hext
      exact hext.1

theorem measurableSet_sausageCompletionEvent
    {d n : ℕ} (rs : List ℕ) (k b : ℕ) :
    MeasurableSet (sausageCompletionEvent d n rs k b) := by
  induction k generalizing rs b with
  | zero => exact measurableSet_sausageGapPrefixEvent d cubicOrigin n rs
  | succ k ih =>
      rw [sausageCompletionEvent]
      exact MeasurableSet.iUnion fun t ↦ MeasurableSet.iUnion fun _ : t ∈ Finset.range b ↦
        ih (rs ++ [t]) (b - (t + 1))

theorem pairwiseDisjoint_sausageCompletionEvent_extensions
    {d n : ℕ} (rs : List ℕ) (k b : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range b) : Set ℕ)
      (fun t ↦ sausageCompletionEvent d n (rs ++ [t]) k (b - (t + 1))) := by
  intro t _ht u _hu htu
  change Disjoint
    (sausageCompletionEvent d n (rs ++ [t]) k (b - (t + 1)))
    (sausageCompletionEvent d n (rs ++ [u]) k (b - (u + 1)))
  apply Set.disjoint_of_subset
    (sausageCompletionEvent_subset_prefix (d := d) (n := n)
      (rs ++ [t]) k (b - (t + 1)))
    (sausageCompletionEvent_subset_prefix (d := d) (n := n)
      (rs ++ [u]) k (b - (u + 1)))
  exact pairwiseDisjoint_sausageGapPrefixEvent_extensions
    (r := max t u) (x := cubicOrigin) (rs := rs)
    (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega)) htu

theorem bernoulliBondMeasure_real_sausageCompletionEvent
    {d n : ℕ} (p : I) (rs : List ℕ) (k b : ℕ) :
    (bernoulliBondMeasure d p).real (sausageCompletionEvent d n rs k b) =
      sausageCompletionMass d p n rs k b := by
  induction k generalizing rs b with
  | zero => rfl
  | succ k ih =>
      rw [sausageCompletionEvent, sausageCompletionMass]
      have hsum := measureReal_biUnion_finset
        (μ := bernoulliBondMeasure d p)
        (pairwiseDisjoint_sausageCompletionEvent_extensions rs k b)
        (fun t _ ↦ measurableSet_sausageCompletionEvent
          (d := d) (n := n) (rs ++ [t]) k (b - (t + 1)))
      rw [hsum]
      apply Finset.sum_congr rfl
      intro t _ht
      exact ih (rs ++ [t]) (b - (t + 1))

/-- Backward-induction comparison of the actual sausage process with iid
renewal gaps having tail `radiusTail`. -/
theorem renewalFitProbability_mul_prefix_le_sausageCompletionMass
    {d n : ℕ} (p : I) (rs : List ℕ) (k b : ℕ)
    (hbudget : rs.sum + rs.length + b ≤ n) :
    renewalFitProbability (radiusTail d p) k b *
        (bernoulliBondMeasure d p).real
          (sausageGapPrefixEvent d cubicOrigin n rs) ≤
      sausageCompletionMass d p n rs k b := by
  induction k generalizing rs b with
  | zero => simp [sausageCompletionMass]
  | succ k ih =>
      rw [sausageCompletionMass]
      calc
        renewalFitProbability (radiusTail d p) (k + 1) b *
            (bernoulliBondMeasure d p).real
              (sausageGapPrefixEvent d cubicOrigin n rs) ≤
            ∑ t ∈ Finset.range b,
              renewalFitProbability (radiusTail d p) k (b - (t + 1)) *
                (bernoulliBondMeasure d p).real
                  (sausageGapPrefixEvent d cubicOrigin n (rs ++ [t])) := by
          apply renewalFitProbability_mul_le_sum_extensions
            (radiusTail d p) (radiusTail_zero d p) (radiusTail_antitone d p)
            (fun qs ↦ (bernoulliBondMeasure d p).real
              (sausageGapPrefixEvent d cubicOrigin n qs)) rs k b
          intro r hr
          have hcdf := sausageGap_conditional_cdf_ge
            (d := d) (n := n) (r := r) p rs (by omega)
          rw [bernoulliBondMeasure_real_sausageGapPrefixNextShortEvent_eq_sum]
            at hcdf
          exact hcdf
        _ ≤ ∑ t ∈ Finset.range b,
              sausageCompletionMass d p n (rs ++ [t]) k (b - (t + 1)) := by
          apply Finset.sum_le_sum
          intro t ht
          apply ih
          have htb := Finset.mem_range.mp ht
          simp only [List.sum_append, List.sum_singleton, List.length_append,
            List.length_singleton]
          omega

/-- The event of having at least `k` pivotals while `Aₙ` occurs. -/
def radiusPivotalCountAtLeastEvent (d : ℕ) (x : Cubic d) (n k : ℕ) :
    Set (EdgeConfiguration d) :=
  {ω | ω ∈ radiusConnectionEvent d x n ∧ k ≤ radiusPivotalCount d x n ω}

theorem sausageCompletionEvent_subset_pivotalCountAtLeast
    {d n : ℕ} (rs : List ℕ) (k b : ℕ)
    (hbudget : rs.sum + rs.length + b ≤ n) :
    sausageCompletionEvent d n rs k b ⊆
      radiusPivotalCountAtLeastEvent d cubicOrigin n (rs.length + k) := by
  induction k generalizing rs b with
  | zero =>
      intro ω hω
      have hprefix := sausageCompletionEvent_subset_prefix rs 0 b hω
      refine ⟨hprefix.1, ?_⟩
      rw [← radiusPivotalDarts_length_eq_count hprefix.1]
      exact sausageGapPrefix_length_le_pivotalDarts_length hprefix (by omega)
  | succ k ih =>
      intro ω hω
      rw [sausageCompletionEvent, Set.mem_iUnion₂] at hω
      obtain ⟨t, ht, hω⟩ := hω
      have htb := Finset.mem_range.mp ht
      have hrec := ih (rs ++ [t]) (b - (t + 1)) (by
        simp only [List.sum_append, List.sum_singleton, List.length_append,
          List.length_singleton]
        omega) hω
      refine ⟨hrec.1, ?_⟩
      have heq : (rs ++ [t]).length + k = rs.length + (k + 1) := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [← heq]
      exact hrec.2

theorem radiusPivotalCount_eq_of_agree
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d}
    (hagree : ∀ e ∈ cubicMetricBallEdges d x n, (e ∈ ω ↔ e ∈ η)) :
    radiusPivotalCount d x n ω = radiusPivotalCount d x n η := by
  classical
  unfold radiusPivotalCount radiusPivotalEdgeFinset
  congr 1
  apply Finset.filter_congr
  intro e _he
  exact isPivotal_radiusConnectionEvent_iff_of_agree hagree e

theorem dependsOn_radiusPivotalCountAtLeastEvent
    (d : ℕ) (x : Cubic d) (n k : ℕ) :
    DependsOn (cubicMetricBallEdges d x n)
      (radiusPivotalCountAtLeastEvent d x n k) := by
  intro ω η hagree
  exact and_congr (dependsOn_radiusConnectionEvent d x n hagree)
    (by rw [radiusPivotalCount_eq_of_agree hagree])

theorem dependsOn_sausageCompletionEvent
    {d n : ℕ} (rs : List ℕ) (k b : ℕ) :
    DependsOn (cubicMetricBallEdges d cubicOrigin n)
      (sausageCompletionEvent d n rs k b) := by
  induction k generalizing rs b with
  | zero => exact dependsOn_sausageGapPrefixEvent d cubicOrigin n rs
  | succ k ih =>
      intro ω η hagree
      simp only [sausageCompletionEvent, Set.mem_iUnion]
      constructor
      · rintro ⟨t, ht, hω⟩
        exact ⟨t, ht, (ih (rs ++ [t]) (b - (t + 1)) hagree).mp hω⟩
      · rintro ⟨t, ht, hη⟩
        exact ⟨t, ht, (ih (rs ++ [t]) (b - (t + 1)) hagree).mpr hη⟩

/-- Integrate a pointwise comparison of finite event-indicator sums under a
Bernoulli product measure. -/
noncomputable def eventIndicatorOne {α : Type*} (A : Set α) (x : α) : ℝ :=
  if x ∈ A then 1 else 0

theorem sum_setBernoulli_real_le_sum_setBernoulli_real_of_indicator
    {ι κ ν : Type*} [DecidableEq ι]
    (p : I) (E : Finset ι) (K : Finset κ) (L : Finset ν)
    (B : κ → Set (Set ι)) (C : ν → Set (Set ι))
    (hB : ∀ i ∈ K, DependsOn E (B i))
    (hC : ∀ j ∈ L, DependsOn E (C j))
    (hpoint : ∀ ω : Set ι,
      (∑ i ∈ K, eventIndicatorOne (B i) ω) ≤
        ∑ j ∈ L, eventIndicatorOne (C j) ω) :
    (∑ i ∈ K, setBer((Set.univ : Set ι), p).real (B i)) ≤
      ∑ j ∈ L, setBer((Set.univ : Set ι), p).real (C j) := by
  classical
  have hleft :
      (∑ i ∈ K, setBer((Set.univ : Set ι), p).real (B i)) =
        ∑ s ∈ E.powerset, finiteBernoulliWeight E (p : ℝ) s *
          ∑ i ∈ K, eventIndicatorOne (B i) (s : Set ι) := by
    calc
      (∑ i ∈ K, setBer((Set.univ : Set ι), p).real (B i)) =
          ∑ i ∈ K, finiteBernoulliProbability E (p : ℝ) (eventTrace (B i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hB i hi |>.setBernoulli_real_eq_finiteBernoulliProbability p
      _ = _ := by
        simp_rw [finiteBernoulliProbability_eq_sum_indicator]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _hs
        rw [← Finset.mul_sum]
        apply congrArg (fun z : ℝ ↦ finiteBernoulliWeight E (p : ℝ) s * z)
        apply Finset.sum_congr rfl
        intro i _hi
        simp [Set.indicator, eventIndicatorOne]
  have hright :
      (∑ j ∈ L, setBer((Set.univ : Set ι), p).real (C j)) =
        ∑ s ∈ E.powerset, finiteBernoulliWeight E (p : ℝ) s *
          ∑ j ∈ L, eventIndicatorOne (C j) (s : Set ι) := by
    calc
      (∑ j ∈ L, setBer((Set.univ : Set ι), p).real (C j)) =
          ∑ j ∈ L, finiteBernoulliProbability E (p : ℝ) (eventTrace (C j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hC j hj |>.setBernoulli_real_eq_finiteBernoulliProbability p
      _ = _ := by
        simp_rw [finiteBernoulliProbability_eq_sum_indicator]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _hs
        rw [← Finset.mul_sum]
        apply congrArg (fun z : ℝ ↦ finiteBernoulliWeight E (p : ℝ) s * z)
        apply Finset.sum_congr rfl
        intro j _hj
        simp [Set.indicator, eventIndicatorOne]
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro s _hs
  exact mul_le_mul_of_nonneg_left (hpoint (s : Set ι))
    (finiteBernoulliWeight_nonneg p.2.1 p.2.2 s)

theorem sum_sausageCompletionEvent_indicator_le_sum_pivotal_indicator
    (d n : ℕ) (ω : EdgeConfiguration d) :
    (∑ k ∈ Finset.Icc 1 n,
        eventIndicatorOne (sausageCompletionEvent d n [] k n) ω) ≤
      ∑ e ∈ cubicMetricBallEdges d cubicOrigin n,
        eventIndicatorOne (radiusConnectionEvent d cubicOrigin n ∩
          pivotalEvent (radiusConnectionEvent d cubicOrigin n) e) ω := by
  classical
  let A := radiusConnectionEvent d cubicOrigin n
  by_cases hA : ω ∈ A
  · have hright :
        (∑ e ∈ cubicMetricBallEdges d cubicOrigin n,
            eventIndicatorOne (A ∩ pivotalEvent A e) ω) =
          radiusPivotalCount d cubicOrigin n ω := by
      rw [radiusPivotalCount, radiusPivotalEdgeFinset, Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro e _he
      simp [eventIndicatorOne, A, hA]
    rw [hright]
    calc
      (∑ k ∈ Finset.Icc 1 n,
          eventIndicatorOne (sausageCompletionEvent d n [] k n) ω) ≤
          ∑ k ∈ Finset.Icc 1 n,
            if k ≤ radiusPivotalCount d cubicOrigin n ω then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hcomp : ω ∈ sausageCompletionEvent d n [] k n
        · have hkN := sausageCompletionEvent_subset_pivotalCountAtLeast
            (d := d) (n := n) [] k n (by simp) hcomp |>.2
          have hkN' : k ≤ radiusPivotalCount d cubicOrigin n ω := by simpa using hkN
          simp [eventIndicatorOne, hcomp, hkN']
        · simp only [eventIndicatorOne, if_neg hcomp]
          split <;> norm_num
      _ = (((Finset.Icc 1 n).filter
          (fun k ↦ k ≤ radiusPivotalCount d cubicOrigin n ω)).card : ℝ) := by
        exact sum_indicator_one_eq_card_filter _ _
      _ ≤ radiusPivotalCount d cubicOrigin n ω := by
        norm_cast
        calc
          ((Finset.Icc 1 n).filter
              (fun k ↦ k ≤ radiusPivotalCount d cubicOrigin n ω)).card ≤
              (Finset.Icc 1 (radiusPivotalCount d cubicOrigin n ω)).card := by
            apply Finset.card_le_card
            intro k hk
            rw [Finset.mem_filter] at hk
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk.1).1, hk.2⟩
          _ = radiusPivotalCount d cubicOrigin n ω := by
            simp [Nat.card_Icc]
  · have hleft :
        (∑ k ∈ Finset.Icc 1 n,
            eventIndicatorOne (sausageCompletionEvent d n [] k n) ω) = 0 := by
      apply Finset.sum_eq_zero
      intro k _hk
      rw [eventIndicatorOne, if_neg]
      intro hcomp
      exact hA (sausageCompletionEvent_subset_prefix [] k n hcomp |>.1)
    rw [hleft]
    apply Finset.sum_nonneg
    intro e _he
    rw [eventIndicatorOne]
    split <;> norm_num

theorem sum_sausageCompletionEvent_probability_le_pivotalNumerator
    (d n : ℕ) (p : I) :
    (∑ k ∈ Finset.Icc 1 n,
        (bernoulliBondMeasure d p).real
          (sausageCompletionEvent d n [] k n)) ≤
      ∑ e ∈ cubicMetricBallEdges d cubicOrigin n,
        (bernoulliBondMeasure d p).real
          (radiusConnectionEvent d cubicOrigin n ∩
            pivotalEvent (radiusConnectionEvent d cubicOrigin n) e) := by
  let E := cubicMetricBallEdges d cubicOrigin n
  have h := sum_setBernoulli_real_le_sum_setBernoulli_real_of_indicator
    p E (Finset.Icc 1 n) E
    (fun k ↦ sausageCompletionEvent d n [] k n)
    (fun e ↦ radiusConnectionEvent d cubicOrigin n ∩
      pivotalEvent (radiusConnectionEvent d cubicOrigin n) e)
    (fun k _ ↦ dependsOn_sausageCompletionEvent [] k n)
    (fun e _ ↦ (dependsOn_radiusConnectionEvent d cubicOrigin n).inter
      ((dependsOn_radiusConnectionEvent d cubicOrigin n).pivotalEvent e))
    (sum_sausageCompletionEvent_indicator_le_sum_pivotal_indicator d n)
  simpa [E, bernoulliBondMeasure] using h

/-- The iid renewal count, multiplied by `P(Aₙ)`, is bounded by the
unconditional pivotal-count numerator.  This is equation (5.21) transferred
to the actual sausage process using Lemma 5.12. -/
theorem finiteRenewalExpectedRenewalCount_mul_radiusTail_le_pivotalNumerator
    (d n : ℕ) (p : I) :
    finiteRenewalExpectedRenewalCount n (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n (radiusTail d p)) * radiusTail d p n ≤
      ∑ e ∈ cubicMetricBallEdges d cubicOrigin n,
        (bernoulliBondMeasure d p).real
          (radiusConnectionEvent d cubicOrigin n ∩
            pivotalEvent (radiusConnectionEvent d cubicOrigin n) e) := by
  calc
    finiteRenewalExpectedRenewalCount n (fun a : Fin (n + 1) ↦ a.1)
        (truncatedTailWeight n (radiusTail d p)) * radiusTail d p n =
        ∑ k ∈ Finset.Icc 1 n,
          renewalFitProbability (radiusTail d p) k n * radiusTail d p n := by
      rw [finiteRenewalExpectedRenewalCount]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [finiteRenewalContinuationProbability_eq_renewalFitProbability
        n k (radiusTail d p) (by
          have := (Finset.mem_Icc.mp hk).2
          omega) (radiusTail_zero d p)]
    _ ≤ ∑ k ∈ Finset.Icc 1 n,
        (bernoulliBondMeasure d p).real
          (sausageCompletionEvent d n [] k n) := by
      apply Finset.sum_le_sum
      intro k _hk
      have hfit := renewalFitProbability_mul_prefix_le_sausageCompletionMass
        (d := d) (n := n) p [] k n (by simp)
      rw [← bernoulliBondMeasure_real_sausageCompletionEvent
        (d := d) (n := n) p [] k n] at hfit
      simpa [sausageGapPrefixEvent, radiusTail] using hfit
    _ ≤ _ := sum_sausageCompletionEvent_probability_le_pivotalNumerator d n p

end Percolation

#print axioms Percolation.finiteRenewalExpectedRenewalCount_mul_radiusTail_le_pivotalNumerator
