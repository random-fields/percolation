import Percolation.Critical.ExponentialDecay
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Right continuity of the percolation probability

Grimmett's proof of Theorem 5.8 uses the soft fact that `θ` is the decreasing infimum of the
finite-radius polynomials `gₚ(n)`.  Hence it is upper semicontinuous; monotonicity then implies
right continuity.
-/

namespace Percolation

open Filter
open MeasureTheory
open scoped unitInterval

theorem continuous_radiusTail_density (d n : ℕ) :
    Continuous (fun p : I ↦ radiusTail d p n) := by
  have heq : (fun p : I ↦ radiusTail d p n) = fun p : I ↦
      finiteBernoulliProbability (cubicMetricBallEdges d cubicOrigin n) p
        (eventTrace (radiusConnectionEvent d cubicOrigin n)) := by
    funext p
    exact DependsOn.bernoulliBondMeasure_real_eq_finiteBernoulliProbability
      (dependsOn_radiusConnectionEvent d cubicOrigin n) p
  rw [heq]
  unfold finiteBernoulliProbability finiteBernoulliExpectation finiteBernoulliWeight
  fun_prop

/-- `θ(p)=infₙ gₚ(n)`. -/
theorem theta_eq_iInf_radiusTail (d : ℕ) (p : I) :
    theta d p = ⨅ n : ℕ, radiusTail d p n := by
  rw [← sInf_range]
  symm
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact Set.range_nonempty _
  · rintro _ ⟨n, rfl⟩
    apply le_of_tendsto (radiusTail_tendsto_theta d p)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact radiusTail_antitone d p hm
  · intro w hw
    have hevent : ∀ᶠ n : ℕ in atTop, radiusTail d p n < w :=
      (radiusTail_tendsto_theta d p) (Iio_mem_nhds hw)
    obtain ⟨n, hn⟩ := hevent.exists
    exact ⟨radiusTail d p n, ⟨n, rfl⟩, hn⟩

theorem theta_upperSemicontinuous (d : ℕ) : UpperSemicontinuous (theta d) := by
  have h : UpperSemicontinuous (fun p : I ↦ ⨅ n : ℕ, radiusTail d p n) :=
    upperSemicontinuous_ciInf
      (fun _ ↦ ⟨0, by rintro _ ⟨n, rfl⟩; exact measureReal_nonneg⟩)
      fun n ↦ (continuous_radiusTail_density d n).upperSemicontinuous
  convert h using 1
  funext p
  exact theta_eq_iInf_radiusTail d p

/-- Right continuity of `θ` on the unit interval, expressed with the right-neighbourhood
filter.  At the endpoint `1` this filter is trivial, as it should be. -/
theorem theta_tendsto_nhdsGT (d : ℕ) (p : I) :
    Tendsto (theta d) (nhdsWithin p (Set.Ioi p)) (nhds (theta d p)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact ha.trans_le (theta_mono d hq.le)
  · intro a ha
    exact Filter.Eventually.filter_mono inf_le_left
      ((upperSemicontinuousAt_iff.mp (theta_upperSemicontinuous d p)) a ha)

end Percolation
