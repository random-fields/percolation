import Percolation.Bernoulli.LSSCountable
import Percolation.Critical.Radius

/-!
# Cubic-lattice application of the LSS finite-cylinder theorem

The graph-metric ball of radius `k` is a concrete uniform cover of every dependence
neighborhood.  Its elementary volume bound supplies the dimension/range constant needed by
the abstract countable LSS construction.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

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

end Percolation
