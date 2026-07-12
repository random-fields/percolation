import Percolation.Critical.LSSCubic
import Percolation.Critical.StaticBlockTranslation

/-!
# LSS comparison for the static good-block field

The good-block law is stationary and `3d`-dependent.  Combining those facts with the cubic
LSS adapter reduces every one-site marginal hypothesis to the origin and yields iid comparison
for the finite-support crossing events used later in Chapter 7.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Finite-cylinder LSS comparison for the `ε`-good block field. -/
theorem epsilonGoodBlockLaw_lss_finiteCylinder_measureReal_le
    (d : ℕ) (hd : 0 < d) (p q : I) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hq : (q : ℝ) < 1)
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p ε n).real
          {η : Set (Cubic d) | cubicOrigin ∈ η})
    {R : Finset (Cubic d)} {A : Set (Set (Cubic d))}
    (hdep : DependsOn R A) (hinc : IsIncreasingEvent A) :
    setBer((Set.univ : Set (Cubic d)), q).real A ≤
      (epsilonGoodBlockLaw d p ε n).real A := by
  apply cubic_lss_finiteCylinder_measureReal_le'
    d (3 * d) hd q hq (epsilonGoodBlockLaw d p ε n)
      (epsilonGoodBlockLaw_kDependent d p ε hn)
  · intro current
    rw [epsilonGoodBlockLaw_real_mem_eq_origin]
    exact hmarginal
  · exact hdep
  · exact hinc

end Percolation
