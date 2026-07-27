import Percolation.Critical.LSSGoodBlocks

namespace Percolation.Chapter7LSSFunctionReview

open MeasureTheory ProbabilityTheory Filter Topology
open scoped unitInterval

/-- Literal source quantifier order on `ℤ^d`. -/
example (d k : ℕ) (hd : 0 < d) :
    ∃ pi : I → I,
      Monotone pi ∧ Tendsto pi (𝓝 (1 : I)) (𝓝 (1 : I)) ∧
      ∀ (delta : I) (mu : Measure (Set (Cubic d))), IsProbabilityMeasure mu →
        KDependent (cubicGraph d) k mu →
        (∀ current : Cubic d,
          (delta : ℝ) ≤ mu.real {eta : Set (Cubic d) | current ∈ eta}) →
        StochasticallyDominates mu setBer((Set.univ : Set (Cubic d)), pi delta) :=
  exists_cubic_lssDominationDensity d k hd

/-- The selected function is nondecreasing. -/
example (B : ℕ) : Monotone (lssDominationDensityUnit B) :=
  monotone_lssDominationDensityUnit B

/-- The selected function tends to one at the source endpoint. -/
example (B : ℕ) :
    Tendsto (lssDominationDensityUnit B) (𝓝 (1 : I)) (𝓝 (1 : I)) :=
  lssDominationDensityUnit_tendsto_one B

/-- Endpoint oracle: zero input gives the all-closed output density. -/
example (B : ℕ) : lssDominationDensityUnit B (0 : I) = 0 :=
  lssDominationDensityUnit_zero B

/-- Endpoint oracle: unit input gives the all-open output density. -/
example (B : ℕ) : lssDominationDensityUnit B (1 : I) = 1 := by
  ext
  exact lssDominationDensityReal_one B

/-- Every law dominates the zero-density iid law. -/
example {V : Type*} [Countable V]
    (mu : Measure (Set V)) [IsProbabilityMeasure mu] :
    StochasticallyDominates mu setBer((Set.univ : Set V), (0 : I)) :=
  stochasticallyDominates_setBernoulli_zero mu

/-- Unit marginals on a denumerable site set force all-open concentration. -/
example {V : Type*} [Countable V] [DecidableEq V]
    (e : ℕ ≃ V) (mu : Measure (Set V)) [IsProbabilityMeasure mu]
    (hmarginal : ∀ v : V, 1 ≤ mu.real {eta : Set V | v ∈ eta}) :
    StochasticallyDominates mu setBer((Set.univ : Set V), (1 : I)) :=
  stochasticallyDominates_setBernoulli_one_of_marginals e mu hmarginal

end Percolation.Chapter7LSSFunctionReview
