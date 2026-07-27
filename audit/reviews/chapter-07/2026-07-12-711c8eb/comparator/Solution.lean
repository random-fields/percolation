import Percolation.Critical.LSSCubic

namespace Review.Chapter07

open Percolation MeasureTheory ProbabilityTheory Filter Topology
open scoped unitInterval

theorem source_7_65 (d k : ℕ) (hd : 0 < d) (_hk : 1 ≤ k) :
    ∃ pi : I → I,
      Monotone pi ∧ Tendsto pi (𝓝 (1 : I)) (𝓝 (1 : I)) ∧
      ∀ (delta : I) (mu : Measure (Set (Cubic d))), IsProbabilityMeasure mu →
        KDependent (cubicGraph d) k mu →
        (∀ x : Cubic d,
          (delta : ℝ) ≤ mu.real {omega : Set (Cubic d) | x ∈ omega}) →
        StochasticallyDominates mu
          setBer((Set.univ : Set (Cubic d)), pi delta) := by
  exact exists_cubic_lssDominationDensity d k hd

end Review.Chapter07
