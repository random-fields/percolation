import Percolation

/-! Producer-drafted source-facing challenges for Grimmett Chapter 6.  The `sorry` terms are
intentional open challenges and are never imported by production or solution files.

This file was **not** authored by the independent reviewer and is not a trusted Comparator
challenge under `AUTOMATED_REVIEW.md`.  It is retained only as a CI-ready draft. -/

namespace Review.Chapter06

open Percolation Set Filter SimpleGraph
open scoped ENNReal unitInterval BigOperators

theorem theorem_6_1 (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hchi : susceptibility d p < ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, boxRadiusTail d p n ≤ Real.exp (-c * n) := by sorry

theorem theorem_6_10 (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ => -Real.log (boxRadiusTail d p n) / n) atTop
      (nhds (boxRadiusDecayRate d p)) := by sorry

theorem theorem_6_14 (d : ℕ) (hd : 2 ≤ d) :
    ContinuousOn (boxRadiusDecayRate d) {p : I | 0 < (p : ℝ)} ∧
      boxRadiusDecayRate d (cubicCriticalProbabilityUnit d hd) = 0 := by sorry

theorem theorem_6_44 (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ n : ℕ, 0 < n →
      c * (p : ℝ) / (n : ℝ) ^ (4 * (d - 1)) *
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ∧
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by sorry

theorem proposition_6_47 (d : ℕ) (hd : 2 ≤ d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ x : Cubic d,
      (x ≠ cubicOrigin →
        lambda * (p : ℝ) ^ (d * cubicL1Dist cubicOrigin x) /
            (cubicL1Dist cubicOrigin x : ℝ) ^ (4 * d * (d - 1)) *
            Real.exp (-(cubicL1Dist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) ≤
          twoPointConnectivity d p cubicOrigin x) ∧
      twoPointConnectivity d p cubicOrigin x ≤
        Real.exp (-(cubicLInfDist cubicOrigin x : ℝ) * boxRadiusDecayRate d p) := by sorry

theorem proposition_6_49 (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d) :
    correlationLength d p ≤ susceptibility d p := by sorry

theorem theorem_6_75 (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      clusterSizeAtLeast d p n ≤ Real.exp (-lambda * n) := by sorry

theorem theorem_6_78 (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < cubicCriticalProbability d) :
    Tendsto (fun n : ℕ => -Real.log (finiteClusterSizeTail d p n) / n) atTop
        (nhds (clusterSizeDecayRate d p)) ∧
      0 < clusterSizeDecayRate d p ∧
      clusterSizeDecayRate d p ≤ boxRadiusDecayRate d p := by sorry

theorem lemma_6_87 {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (W : Finset V) (hW : W.Nonempty) :
    ∃ w ∈ W, ∀ x, x ∈ W → x ≠ w → ∀ y, y ∈ W → y ≠ w →
      (G.deleteIncidenceSet w).Reachable x y := by sorry

theorem lemma_6_89 (d : ℕ) (p : I) (x₀ x₁ x₂ : Cubic d) :
    bernoulliBondMeasure d p (threePointConnectionEvent d x₀ x₁ x₂) ≤
      ∑' u : Cubic d, twoPointConnectivityENNReal d p u x₀ *
        twoPointConnectivityENNReal d p u x₁ * twoPointConnectivityENNReal d p u x₂ := by sorry

theorem theorem_6_93 (d n : ℕ) (p : I) (x : Fin (n + 3) → Cubic d) :
    bernoulliBondMeasure d p (orderedMultiPointConnectionEvent d n x) ≤
      ∑' s : CubicConnectivitySkeleton (n + 3),
        ∑' psi : s.Vertex → Cubic d, skeletonConnectivityWeight p s psi x := by sorry

theorem lemma_6_102 (d m n : ℕ) (p : I) (hd : 0 < d) (hm : 0 < m) (hn : 0 < n)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (p : ℝ) * (1 - (p : ℝ))⁻¹ ^ 2 * (finiteClusterSizeProbability d p m / m) *
        (finiteClusterSizeProbability d p n / n) ≤
      finiteClusterSizeProbability d p (m + n) / (m + n) := by sorry

theorem theorem_6_108 (d : ℕ) (hd : 2 ≤ d) :
    AnalyticOnNhd ℝ (concreteClusterDensitySeries d)
        (Ico (0 : ℝ) (cubicCriticalProbability d)) ∧
      AnalyticOnNhd ℝ (concreteSusceptibilitySeries d)
        (Ico (0 : ℝ) (cubicCriticalProbability d)) := by sorry

end Review.Chapter06
