import Percolation.Bernoulli.LSSDominationFunction
import Percolation.Critical.Radius

/-!
# Cubic-lattice application of the LSS theorem

The graph-metric ball of radius `k` is a concrete uniform cover of every dependence
neighborhood.  Its elementary volume bound supplies the dimension/range constant needed by
the abstract countable LSS construction.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped unitInterval

/-- A fixed enumeration of `ℤ^d` in every positive dimension. -/
noncomputable def cubicNatEquiv (d : ℕ) (hd : 0 < d) : ℕ ≃ Cubic d := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  letI : Infinite (Cubic d) := Pi.infinite_of_right
  letI : Denumerable (Cubic d) := Denumerable.ofEncodableOfInfinite (Cubic d)
  exact Denumerable.equiv₂ ℕ (Cubic d)

/-- The cubic graph-metric ball covers every vertex at extended distance at most `k`. -/
theorem mem_cubicMetricBall_of_edist_le
    {d k : ℕ} {x y : Cubic d}
    (hxy : (cubicGraph d).edist x y ≤ k) :
    y ∈ cubicMetricBall d x k := by
  obtain ⟨w⟩ := nonempty_cubicWalk d x y
  have hreach : (cubicGraph d).Reachable x y := ⟨w⟩
  rw [← hreach.coe_dist_eq_edist, cubicGraph_dist_eq_l1Dist] at hxy
  exact mem_cubicMetricBall_iff_l1Dist_le.mpr (by exact_mod_cast hxy)

/-- Uniform prefix-neighborhood bound for the cubic dependency graph. -/
theorem cubic_enumerationPrefixDependencyGraph_neighbor_card_le
    (d k : ℕ) (e : ℕ ≃ Cubic d) :
    ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph (cubicGraph d) k e n).edist current x ≤ 1).card ≤
        3 ^ d * (k + 1) ^ d := by
  apply enumerationPrefixDependencyGraph_neighbor_card_le
    (cubicGraph d) k (3 ^ d * (k + 1) ^ d) e
    (fun x ↦ cubicMetricBall d x k)
  · intro x y hxy
    exact mem_cubicMetricBall_of_edist_le hxy
  · intro x
    exact cubicMetricBall_card_le d x k

/-- Cubic-lattice LSS comparison for increasing finite-cylinder events, with the explicit
uniform neighborhood constant. -/
theorem cubic_lss_finiteCylinder_measureReal_le
    (d k : ℕ) (e : ℕ ≃ Cubic d)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set (Cubic d))) [IsProbabilityMeasure mu]
    (hmu : KDependent (cubicGraph d) k mu)
    (hmarginal : ∀ current : Cubic d,
      (lssMarginalThresholdUnit (3 ^ d * (k + 1) ^ d) q hq : ℝ) ≤
        mu.real {original : Set (Cubic d) | current ∈ original})
    {R : Finset (Cubic d)} {A : Set (Set (Cubic d))}
    (hdep : DependsOn R A) (hinc : IsIncreasingEvent A) :
    setBer((Set.univ : Set (Cubic d)), q).real A ≤ mu.real A := by
  exact lss_finiteCylinder_measureReal_le
    (cubicGraph d) k (3 ^ d * (k + 1) ^ d) e
    (cubic_enumerationPrefixDependencyGraph_neighbor_card_le d k e)
    q hq mu hmu hmarginal hdep hinc

/-- Source-facing positive-dimensional form with the canonical cubic enumeration hidden. -/
theorem cubic_lss_finiteCylinder_measureReal_le'
    (d k : ℕ) (hd : 0 < d)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set (Cubic d))) [IsProbabilityMeasure mu]
    (hmu : KDependent (cubicGraph d) k mu)
    (hmarginal : ∀ current : Cubic d,
      (lssMarginalThresholdUnit (3 ^ d * (k + 1) ^ d) q hq : ℝ) ≤
        mu.real {original : Set (Cubic d) | current ∈ original})
    {R : Finset (Cubic d)} {A : Set (Set (Cubic d))}
    (hdep : DependsOn R A) (hinc : IsIncreasingEvent A) :
    setBer((Set.univ : Set (Cubic d)), q).real A ≤ mu.real A :=
  cubic_lss_finiteCylinder_measureReal_le
    d k (cubicNatEquiv d hd) q hq mu hmu hmarginal hdep hinc

/-- Cubic-lattice LSS domination in the full expectation formulation. -/
theorem cubic_lss_stochasticallyDominates
    (d k : ℕ) (e : ℕ ≃ Cubic d)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set (Cubic d))) [IsProbabilityMeasure mu]
    (hmu : KDependent (cubicGraph d) k mu)
    (hmarginal : ∀ current : Cubic d,
      (lssMarginalThresholdUnit (3 ^ d * (k + 1) ^ d) q hq : ℝ) ≤
        mu.real {original : Set (Cubic d) | current ∈ original}) :
    StochasticallyDominates mu setBer((Set.univ : Set (Cubic d)), q) := by
  exact lss_stochasticallyDominates
    (cubicGraph d) k (3 ^ d * (k + 1) ^ d) e
    (cubic_enumerationPrefixDependencyGraph_neighbor_card_le d k e)
    q hq mu hmu hmarginal

/-- Source-facing positive-dimensional cubic LSS theorem with the enumeration hidden. -/
theorem cubic_lss_stochasticallyDominates'
    (d k : ℕ) (hd : 0 < d)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set (Cubic d))) [IsProbabilityMeasure mu]
    (hmu : KDependent (cubicGraph d) k mu)
    (hmarginal : ∀ current : Cubic d,
      (lssMarginalThresholdUnit (3 ^ d * (k + 1) ^ d) q hq : ℝ) ≤
        mu.real {original : Set (Cubic d) | current ∈ original}) :
    StochasticallyDominates mu setBer((Set.univ : Set (Cubic d)), q) :=
  cubic_lss_stochasticallyDominates
    d k (cubicNatEquiv d hd) q hq mu hmu hmarginal

/-- Threshold form of finite-cylinder LSS domination on `ℤ^d`. -/
theorem exists_cubic_lssFiniteCylinderDominationThreshold
    (d k : ℕ) (hd : 0 < d) (q : I) (hq : (q : ℝ) < 1) :
    ∃ delta : I, (delta : ℝ) < 1 ∧
      ∀ (mu : Measure (Set (Cubic d))), IsProbabilityMeasure mu →
        KDependent (cubicGraph d) k mu →
        (∀ current : Cubic d,
          (delta : ℝ) ≤
            mu.real {original : Set (Cubic d) | current ∈ original}) →
        ∀ (R : Finset (Cubic d)) (A : Set (Set (Cubic d))),
          DependsOn R A → IsIncreasingEvent A →
            setBer((Set.univ : Set (Cubic d)), q).real A ≤ mu.real A := by
  exact exists_lssFiniteCylinderDominationThreshold
    (cubicGraph d) k (3 ^ d * (k + 1) ^ d) (cubicNatEquiv d hd)
    (cubic_enumerationPrefixDependencyGraph_neighbor_card_le
      d k (cubicNatEquiv d hd)) q hq

/-- Source-style threshold form of Theorem 7.65 on `ℤ^d`. -/
theorem exists_cubic_lssDominationThreshold
    (d k : ℕ) (hd : 0 < d) (q : I) (hq : (q : ℝ) < 1) :
    ∃ delta : I, (delta : ℝ) < 1 ∧
      ∀ (mu : Measure (Set (Cubic d))), IsProbabilityMeasure mu →
        KDependent (cubicGraph d) k mu →
        (∀ current : Cubic d,
          (delta : ℝ) ≤
            mu.real {original : Set (Cubic d) | current ∈ original}) →
        StochasticallyDominates mu setBer((Set.univ : Set (Cubic d)), q) := by
  exact exists_lssDominationThreshold
    (cubicGraph d) k (3 ^ d * (k + 1) ^ d) (cubicNatEquiv d hd)
    (cubic_enumerationPrefixDependencyGraph_neighbor_card_le
      d k (cubicNatEquiv d hd)) q hq

/-- Literal function-valued form of Theorem 7.65 on `ℤ^d`: one monotone output-density
function works at every input marginal density and tends to one at density one. -/
theorem exists_cubic_lssDominationDensity
    (d k : ℕ) (hd : 0 < d) :
    ∃ pi : I → I,
      Monotone pi ∧ Tendsto pi (𝓝 (1 : I)) (𝓝 (1 : I)) ∧
      ∀ (delta : I) (mu : Measure (Set (Cubic d))), IsProbabilityMeasure mu →
        KDependent (cubicGraph d) k mu →
        (∀ current : Cubic d,
          (delta : ℝ) ≤
            mu.real {original : Set (Cubic d) | current ∈ original}) →
        StochasticallyDominates mu
          setBer((Set.univ : Set (Cubic d)), pi delta) := by
  exact exists_lssDominationDensity
    (cubicGraph d) k (3 ^ d * (k + 1) ^ d) (cubicNatEquiv d hd)
    (cubic_enumerationPrefixDependencyGraph_neighbor_card_le
      d k (cubicNatEquiv d hd))

end Percolation
