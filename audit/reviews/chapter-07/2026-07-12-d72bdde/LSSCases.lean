import Percolation.Critical.LSSGoodBlocks

namespace Percolation.Chapter7LSSReview

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The semantic review event really lies beyond the finite-cylinder theorem. -/
theorem infiniteSiteEvent_not_dependsOn_finset
    {V : Type*} [Infinite V] [DecidableEq V] :
    ¬ ∃ R : Finset V, DependsOn R {eta : Set V | eta.Infinite} := by
  rintro ⟨R, hR⟩
  let xi : Set V := (R : Set V)ᶜ
  have hxi : xi.Infinite := R.finite_toSet.infinite_compl
  have hagree : ∀ v ∈ R, (v ∈ (∅ : Set V) ↔ v ∈ xi) := by
    intro v hv
    simp [xi, hv]
  have hiff := hR hagree
  have hemptyInfinite := hiff.mpr hxi
  simp at hemptyInfinite

/-- Full LSS domination compares an increasing event with no finite support. -/
example {V : Type*} [Countable V] [Infinite V] [DecidableEq V]
    (G : SimpleGraph V) (k B : ℕ) (e : ℕ ≃ V)
    (hneighbor : ∀ n (current : Fin n),
      (Finset.univ.filter fun x ↦
        (enumerationPrefixDependencyGraph G k e n).edist current x ≤ 1).card ≤ B)
    (q : I) (hq : (q : ℝ) < 1)
    (mu : Measure (Set V)) [IsProbabilityMeasure mu]
    (hmu : KDependent G k mu)
    (hmarginal : ∀ current : V,
      (lssMarginalThresholdUnit B q hq : ℝ) ≤
        mu.real {eta : Set V | current ∈ eta}) :
    setBer((Set.univ : Set V), q).real {eta : Set V | eta.Infinite} ≤
      mu.real {eta : Set V | eta.Infinite} := by
  exact (lss_stochasticallyDominates
    G k B e hneighbor q hq mu hmu hmarginal).measureReal_le
      MeasurableSet.setOf_infinite (fun _eta _xi hsub hinf => hinf.mono hsub)

/-- Event comparison extracted from the expectation-form conclusion has the source orientation:
the dependent high-density field is the dominating law. -/
example {V : Type*} [Countable V] [DecidableEq V]
    (mu : Measure (Set V)) [IsProbabilityMeasure mu] (q : I)
    (hdom : StochasticallyDominates mu setBer((Set.univ : Set V), q))
    (v : V) :
    (q : ℝ) ≤ mu.real {eta : Set V | v ∈ eta} := by
  have hle := hdom.measureReal_le (measurableSet_mem v)
    (fun _eta _xi hsub hv => hsub hv)
  rw [show {eta : Set V | v ∈ eta} =
      {eta : Set V | (({v} : Finset V) : Set V) ⊆ eta} by
    ext eta
    simp] at hle
  rw [setBernoulli_real_superset_finset_univ] at hle
  simpa using hle

end Percolation.Chapter7LSSReview
