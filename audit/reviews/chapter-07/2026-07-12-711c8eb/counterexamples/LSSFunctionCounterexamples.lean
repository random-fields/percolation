import Percolation.Bernoulli.LSSDominationFunction

namespace Percolation.Chapter7LSSFunctionReview

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Anti-target: no iid law of density below one can dominate iid density one, already on one
site. Thus the old fixed-target theorem genuinely needs `q<1`; the repaired function-valued
theorem handles input density one separately. -/
theorem not_iid_stochasticallyDominates_density_one
    (delta : I) (hdelta : (delta : ℝ) < 1) :
    ¬ StochasticallyDominates
      setBer((Set.univ : Set Unit), delta)
      setBer((Set.univ : Set Unit), (1 : I)) := by
  intro hdom
  have hle := hdom.measureReal_le (measurableSet_mem ())
    (show IsIncreasingEvent {eta : Set Unit | () ∈ eta} by
      intro eta xi hetaxi heta
      exact hetaxi heta)
  have hprob (p : I) :
      setBer((Set.univ : Set Unit), p).real {eta : Set Unit | () ∈ eta} = (p : ℝ) := by
    rw [show {eta : Set Unit | () ∈ eta} =
        {eta : Set Unit | (({()} : Finset Unit) : Set Unit) ⊆ eta} by
      ext eta
      simp]
    simpa using setBernoulli_real_superset_finset_univ ({()} : Finset Unit) p
  rw [hprob, hprob] at hle
  norm_num at hle
  exact (not_le_of_gt hdelta) hle

end Percolation.Chapter7LSSFunctionReview
