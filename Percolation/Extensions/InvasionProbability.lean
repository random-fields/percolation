import Percolation.Extensions.Invasion
import Percolation.Bernoulli.Coupling
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The iid continuous-label law for invasion percolation
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set

private theorem uniformProduct_diagonal_measure_zero :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))
        {z : ℝ × ℝ | z.1 = z.2} = 0 := by
  apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
  filter_upwards [] with x
  have hsection : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_diagonal_iff, Set.mem_singleton_iff]
    constructor <;> intro h <;> exact h.symm
  rw [hsection]
  exact measure_singleton x

theorem couplingMeasure_pair_eq_zero {ι : Type*} {i j : ι} (hij : i ≠ j) :
    couplingMeasure ι {X | X i = X j} = 0 := by
  let ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hiIndep : iIndepFun (fun (k : ι) (X : ι → ℝ) ↦ X k) (couplingMeasure ι) := by
    rw [couplingMeasure]
    exact iIndepFun_infinitePi (X := fun (_ : ι) ↦ (id : ℝ → ℝ))
      fun _ ↦ measurable_id
  have hpair := (hiIndep.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  have hmarginal (k : ι) :
      (couplingMeasure ι).map (fun X : ι → ℝ ↦ X k) = ν := by
    exact Measure.infinitePi_map_eval (fun _ : ι ↦ ν) k
  rw [hmarginal i, hmarginal j] at hpair
  have hdiag : MeasurableSet {z : ℝ × ℝ | z.1 = z.2} := measurableSet_diagonal
  have hpre : (fun X : ι → ℝ ↦ (X i, X j)) ⁻¹'
      {z : ℝ × ℝ | z.1 = z.2} = {X | X i = X j} := rfl
  rw [← hpre, ← Measure.map_apply (by fun_prop) hdiag, hpair]
  exact uniformProduct_diagonal_measure_zero

/-- Iid uniform labels have no ties, simultaneously for every pair of edges. -/
theorem couplingMeasure_ae_pairwise_distinct {ι : Type*} [Countable ι] :
    ∀ᵐ X : ι → ℝ ∂couplingMeasure ι, ∀ i j, i ≠ j → X i ≠ X j := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · have hzero := couplingMeasure_pair_eq_zero hij
    have hae : ∀ᵐ X : ι → ℝ ∂couplingMeasure ι, X ∉ {X | X i = X j} :=
      measure_eq_zero_iff_ae_notMem.1 hzero
    filter_upwards [hae] with X hX
    exact fun _ hEq ↦ hX hEq

/-- Source-facing specialization: the canonical tie-break is almost surely never used. -/
theorem invasionLabels_ae_pairwise_distinct {d : ℕ} :
    ∀ᵐ label : CubicEdge d → ℝ ∂couplingMeasure (CubicEdge d),
      ∀ e f, e ≠ f → label e ≠ label f :=
  couplingMeasure_ae_pairwise_distinct

end Percolation
