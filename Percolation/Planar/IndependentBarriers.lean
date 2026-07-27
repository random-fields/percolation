import Percolation.Bernoulli.FKGInfinite

/-!
# Independent planar barriers

This file isolates the probability-theoretic part of the critical square-lattice argument.
Planar geometry supplies finite, mutually independent barrier events on disjoint annuli.  A
uniform positive lower bound for those barriers forces the origin percolation probability to
vanish.  No planar-topology assumption is used in this module.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval

/-- Uniformly positive independent barriers which every infinite origin cluster must avoid force
the origin percolation probability to vanish.  This is the countable-annulus probability kernel
behind the RSW proof of Grimmett, Lemma 11.12. -/
theorem theta_eq_zero_of_iIndep_barriers
    {d : ℕ} (p : I) (barrier : ℕ → Set (EdgeConfiguration d))
    (hmeas : ∀ n, MeasurableSet (barrier n))
    (hind : iIndepSet barrier (bernoulliBondMeasure d p))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hprob : ∀ n, δ ≤ (bernoulliBondMeasure d p).real (barrier n))
    (hblock : { ω | hasInfiniteOpenCluster d ω } ⊆ ⋂ n, (barrier n)ᶜ) :
    theta d p = 0 := by
  let μ := bernoulliBondMeasure d p
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, bernoulliBondMeasure]
    infer_instance
  have hindCompl : iIndepSet (fun n ↦ (barrier n)ᶜ) μ :=
    iIndepSet_compl hind
  have hfinite (N : ℕ) :
      theta d p ≤ (1 - δ) ^ N := by
    have hsubset : { ω | hasInfiniteOpenCluster d ω } ⊆
        ⋂ n ∈ Finset.range N, (barrier n)ᶜ := by
      intro ω hω
      simp only [Set.mem_iInter]
      intro n _hn
      exact Set.mem_iInter.mp (hblock hω) n
    have hfactorMeasure := hindCompl.meas_biInter (Finset.range N)
    have hfactor :
        μ.real (⋂ n ∈ Finset.range N, (barrier n)ᶜ) =
          ∏ n ∈ Finset.range N, μ.real ((barrier n)ᶜ) := by
      simpa only [measureReal_def, ENNReal.toReal_prod] using
        congrArg ENNReal.toReal hfactorMeasure
    calc
      theta d p = μ.real { ω | hasInfiniteOpenCluster d ω } := rfl
      _ ≤ μ.real (⋂ n ∈ Finset.range N, (barrier n)ᶜ) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ = ∏ n ∈ Finset.range N, μ.real ((barrier n)ᶜ) := hfactor
      _ ≤ ∏ _n ∈ Finset.range N, (1 - δ) := by
        apply Finset.prod_le_prod
        · intro n _hn
          exact measureReal_nonneg
        · intro n _hn
          rw [measureReal_compl (hmeas n), probReal_univ]
          linarith [hprob n]
      _ = (1 - δ) ^ N := by simp
  have hbase0 : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hbase1 : 1 - δ < 1 := sub_lt_self 1 hδ0
  have hlim : Tendsto (fun N : ℕ ↦ (1 - δ) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  exact le_antisymm
    (ge_of_tendsto hlim (Filter.Eventually.of_forall hfinite))
    measureReal_nonneg

end Percolation
