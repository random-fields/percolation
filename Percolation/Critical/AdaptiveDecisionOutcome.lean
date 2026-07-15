import Percolation.Critical.FiniteExplorationBellman

/-!
# Concrete events represented by adaptive decision trees

The finite Bellman comparison produces a sum of exact-history masses.  This file identifies that
sum with the measure of a concrete finite union.  The key point is semantic, not merely algebraic:
distinct Boolean leaves of a deterministic adaptive query tree are disjoint events even though
the queried vertex at a later time depends on the preceding answers.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open Classical

namespace AdaptiveSiteExploration

variable {V Omega : Type*}

/-- Exact event represented by one Boolean leaf of a depth-`n` adaptive query tree. -/
def adaptiveDecisionLeafEvent
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) {n : ℕ} (bits : Fin n → Bool) : Set Omega :=
  adaptiveAnswerHistoryEvent answer
    (adaptiveQueryHistory query (List.ofFn bits))

/-- The unique Boolean leaf selected by `omega` in a depth-`n` adaptive query tree. -/
def adaptiveDecisionBits
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) (omega : Omega) :
    ∀ n : ℕ, Fin n → Bool
  | 0 => Fin.elim0
  | n + 1 =>
      let bits := adaptiveDecisionBits answer query omega n
      let history := adaptiveQueryHistory query (List.ofFn bits)
      Fin.snoc bits (answer omega history (query history))

theorem adaptiveDecisionLeafEvent_snoc
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) {n : ℕ}
    (bits : Fin n → Bool) (b : Bool) :
    adaptiveDecisionLeafEvent answer query (Fin.snoc bits b) =
      adaptiveDecisionLeafEvent answer query bits ∩
        {omega | answer omega
          (adaptiveQueryHistory query (List.ofFn bits))
          (query (adaptiveQueryHistory query (List.ofFn bits))) = b} := by
  rw [adaptiveDecisionLeafEvent, adaptiveDecisionLeafEvent,
    adaptiveQueryHistory_ofFn_snoc,
    adaptiveAnswerHistoryEvent_append_singleton]

theorem adaptiveDecisionLeafEvent_snoc_subset
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) {n : ℕ}
    (bits : Fin n → Bool) (b : Bool) :
    adaptiveDecisionLeafEvent answer query (Fin.snoc bits b) ⊆
      adaptiveDecisionLeafEvent answer query bits := by
  rw [adaptiveDecisionLeafEvent_snoc]
  exact Set.inter_subset_left

/-- Every sample belongs to the unique adaptive leaf obtained by replaying its answers. -/
theorem mem_adaptiveDecisionLeafEvent_adaptiveDecisionBits
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) (omega : Omega) :
    ∀ n, omega ∈ adaptiveDecisionLeafEvent answer query
      (adaptiveDecisionBits answer query omega n) := by
  intro n
  induction n with
  | zero =>
      simp [adaptiveDecisionBits, adaptiveDecisionLeafEvent, adaptiveQueryHistory]
  | succ n ih =>
      rw [show adaptiveDecisionBits answer query omega (n + 1) =
          Fin.snoc (adaptiveDecisionBits answer query omega n)
            (answer omega
              (adaptiveQueryHistory query
                (List.ofFn (adaptiveDecisionBits answer query omega n)))
              (query (adaptiveQueryHistory query
                (List.ofFn (adaptiveDecisionBits answer query omega n))))) by rfl,
        adaptiveDecisionLeafEvent_snoc]
      exact ⟨ih, rfl⟩

theorem adaptiveDecisionLeafEvent_snoc_true_disjoint_false
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) {n : ℕ}
    (bits : Fin n → Bool) :
    Disjoint
      (adaptiveDecisionLeafEvent answer query (Fin.snoc bits true))
      (adaptiveDecisionLeafEvent answer query (Fin.snoc bits false)) := by
  rw [adaptiveDecisionLeafEvent, adaptiveDecisionLeafEvent,
    adaptiveQueryHistory_ofFn_snoc, adaptiveQueryHistory_ofFn_snoc]
  exact adaptiveAnswerHistoryEvent_append_true_disjoint_false answer
    (adaptiveQueryHistory query (List.ofFn bits))
    (query (adaptiveQueryHistory query (List.ofFn bits)))

/-- Distinct leaves of a deterministic adaptive query tree are disjoint. -/
theorem adaptiveDecisionLeafEvent_disjoint_of_ne
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) :
    ∀ {n : ℕ} (x y : Fin n → Bool), x ≠ y →
      Disjoint (adaptiveDecisionLeafEvent answer query x)
        (adaptiveDecisionLeafEvent answer query y) := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      exfalso
      apply hxy
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro x y hxy
      let xInit := Fin.init x
      let yInit := Fin.init y
      let xLast := x (Fin.last n)
      let yLast := y (Fin.last n)
      have hx : Fin.snoc xInit xLast = x := Fin.snoc_init_self x
      have hy : Fin.snoc yInit yLast = y := Fin.snoc_init_self y
      by_cases hinit : xInit = yInit
      · have hlast : xLast ≠ yLast := by
          intro hlast
          apply hxy
          rw [← hx, ← hy, hinit, hlast]
        rw [← hx, ← hy]
        cases hxl : xLast <;> cases hyl : yLast
        · exact False.elim (hlast (by simp [hxl, hyl]))
        · simpa only [hinit] using
            (adaptiveDecisionLeafEvent_snoc_true_disjoint_false answer query xInit).symm
        · simpa only [hinit] using
            adaptiveDecisionLeafEvent_snoc_true_disjoint_false answer query xInit
        · exact False.elim (hlast (by simp [hxl, hyl]))
      · have hdisj := ih xInit yInit hinit
        rw [← hx, ← hy]
        exact hdisj.mono
          (adaptiveDecisionLeafEvent_snoc_subset answer query xInit xLast)
          (adaptiveDecisionLeafEvent_snoc_subset answer query yInit yLast)

theorem pairwiseDisjoint_adaptiveDecisionLeafEvent
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V) (n : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin n → Bool))
      (adaptiveDecisionLeafEvent answer query) := by
  intro x _hx y _hy hxy
  exact adaptiveDecisionLeafEvent_disjoint_of_ne answer query x y hxy

/-- Concrete union of the winning leaves at a fixed decision-tree depth. -/
def adaptiveDecisionWinEvent
    (answer : Omega → List (V × Bool) → V → Bool)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop) (n : ℕ) : Set Omega :=
  ⋃ bits : Fin n → Bool, ⋃ (_hwin :
      win (adaptiveQueryHistory query (List.ofFn bits))),
    adaptiveDecisionLeafEvent answer query bits

theorem measurableSet_adaptiveDecisionWinEvent
    [MeasurableSpace Omega]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop) (n : ℕ) :
    MeasurableSet (adaptiveDecisionWinEvent answer query win n) := by
  unfold adaptiveDecisionWinEvent
  apply MeasurableSet.iUnion
  intro bits
  apply MeasurableSet.iUnion
  intro _hwin
  exact measurableSet_adaptiveAnswerHistoryEvent hanswer _

/-- The abstract winning mass is exactly the probability of the concrete winning-leaf union. -/
theorem measureReal_adaptiveDecisionWinEvent
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {answer : Omega → List (V × Bool) → V → Bool}
    (hanswer : MeasurableAnswer answer)
    (query : List (V × Bool) → V)
    (win : List (V × Bool) → Prop) (n : ℕ) :
    mu.real (adaptiveDecisionWinEvent answer query win n) =
      adaptiveDecisionWinMass mu answer query win [] n := by
  classical
  let winning : Finset (Fin n → Bool) :=
    Finset.univ.filter fun bits ↦ win (adaptiveQueryHistory query (List.ofFn bits))
  have hrepr : adaptiveDecisionWinEvent answer query win n =
      ⋃ bits ∈ winning, adaptiveDecisionLeafEvent answer query bits := by
    ext omega
    simp [adaptiveDecisionWinEvent, winning]
  rw [hrepr, measureReal_biUnion_finset]
  · rw [adaptiveDecisionWinMass]
    simp only [winning, adaptiveDecisionLeafEvent, adaptiveQueryHistory,
      Finset.sum_filter]
  · intro x _hx y _hy hxy
    exact adaptiveDecisionLeafEvent_disjoint_of_ne answer query x y hxy
  · intro bits _hbits
    exact measurableSet_adaptiveAnswerHistoryEvent hanswer _

end AdaptiveSiteExploration

end Percolation
