import Percolation.Bernoulli.Russo

/-!
# Continuity of finite-cylinder probabilities

Every event determined by finitely many Bernoulli coordinates has a polynomial probability.
This endpoint-safe continuity theorem is used when the half-space argument moves a reliable
finite brick event from `p_c` to a slightly smaller density.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

theorem continuous_finiteBernoulliProbability {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (T : Set (Finset ι)) :
    Continuous fun x : ℝ ↦ finiteBernoulliProbability E x T := by
  unfold finiteBernoulliProbability finiteBernoulliExpectation finiteBernoulliWeight
  fun_prop

/-- Probability of a finite-cylinder event is continuous in the density, including both
endpoints through the canonical projection to `[0,1]`. -/
theorem DependsOn.continuous_setBernoulli_real {ι : Type*} [Countable ι] [DecidableEq ι]
    {E : Finset ι} {A : Set (Set ι)} (hA : DependsOn E A) :
    Continuous fun x : ℝ ↦
      setBer((Set.univ : Set ι), Set.projIcc 0 1 zero_le_one x).real A := by
  have heq : (fun x : ℝ ↦
      setBer((Set.univ : Set ι), Set.projIcc 0 1 zero_le_one x).real A) =
      fun x : ℝ ↦ finiteBernoulliProbability E
        (((Set.projIcc 0 1 zero_le_one x : I) : ℝ)) (eventTrace A) := by
    funext x
    exact hA.setBernoulli_real_eq_finiteBernoulliProbability
      (Set.projIcc 0 1 zero_le_one x)
  rw [heq]
  exact (continuous_finiteBernoulliProbability E (eventTrace A)).comp (by fun_prop)

/-- Cubic bond-percolation specialization. -/
theorem DependsOn.continuous_bernoulliBondMeasure_real {d : ℕ}
    {E : Finset (CubicEdge d)} {A : Set (EdgeConfiguration d)} (hA : DependsOn E A) :
    Continuous fun x : ℝ ↦
      (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one x)).real A := by
  simpa [bernoulliBondMeasure] using hA.continuous_setBernoulli_real

/-- A strict inequality for a continuous function at a positive unit-interval point persists at
some strictly smaller unit-interval point.  This is the endpoint bookkeeping used in the
half-space contradiction argument. -/
theorem exists_unitInterval_lt_of_continuous_gt
    {f : ℝ → ℝ} (hf : Continuous f) {p : I} (hp0 : 0 < (p : ℝ))
    {a : ℝ} (ha : a < f p) :
    ∃ q : I, (q : ℝ) < (p : ℝ) ∧ a < f q := by
  have hopen : IsOpen {x : ℝ | a < f x} := isOpen_lt continuous_const hf
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (p : ℝ) ha
  let δ : ℝ := min ((p : ℝ) / 2) (ε / 2)
  have hδ : 0 < δ := by
    exact lt_min (half_pos hp0) (half_pos hε)
  have hδp : δ ≤ (p : ℝ) / 2 := min_le_left _ _
  have hδε : δ < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  have hq0 : 0 ≤ (p : ℝ) - δ := by linarith
  have hq1 : (p : ℝ) - δ ≤ 1 := by linarith [p.2.2]
  let q : I := ⟨(p : ℝ) - δ, hq0, hq1⟩
  refine ⟨q, by simp [q]; linarith, ?_⟩
  apply hball
  simp only [Metric.mem_ball, Real.dist_eq, q]
  rw [show (p : ℝ) - δ - (p : ℝ) = -δ by ring, abs_neg, abs_of_nonneg hδ.le]
  exact hδε

end Percolation
