import Percolation.Critical.BoxTrifurcation
import Percolation.Critical.ThetaContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.LeftRight

/-!
# Continuity in the supercritical phase

This file contains the source-facing continuity interfaces from Grimmett Chapter 8.
-/

namespace Percolation

open Filter
open MeasureTheory
open scoped Topology unitInterval

/-- The origin-percolation event at density `p`, realized on the common uniform-coupling
probability space. -/
def coupledInfiniteClusterEvent (d : ℕ) (p : I) :
    Set (CubicEdge d → ℝ) :=
  thresholdConfiguration p ⁻¹'
    {omega : EdgeConfiguration d | hasInfiniteOpenCluster d omega}

theorem measurableSet_coupledInfiniteClusterEvent (d : ℕ) (p : I) :
    MeasurableSet (coupledInfiniteClusterEvent d p) :=
  (measurableSet_hasInfiniteOpenCluster d).preimage
    (measurable_thresholdConfiguration p)

/-- The coupled origin-percolation event has probability `θ(p)`. -/
theorem couplingMeasure_real_coupledInfiniteClusterEvent (d : ℕ) (p : I) :
    (couplingMeasure (CubicEdge d)).real (coupledInfiniteClusterEvent d p) =
      theta d p := by
  unfold coupledInfiniteClusterEvent theta bernoulliBondMeasure
  rw [← couplingMeasure_map_thresholdConfiguration (ι := CubicEdge d) p]
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_thresholdConfiguration p)
    (measurableSet_hasInfiniteOpenCluster d)]

/-- A Bernoulli probability-one event also occurs almost surely after thresholding the common
uniform coupling. -/
theorem couplingMeasure_ae_thresholdConfiguration_mem_of_measureReal_eq_one
    {d : ℕ} {p : I} {A : Set (EdgeConfiguration d)} (hA : MeasurableSet A)
    (hAone : (bernoulliBondMeasure d p).real A = 1) :
    ∀ᵐ X ∂couplingMeasure (CubicEdge d), thresholdConfiguration p X ∈ A := by
  change ∀ᵐ X ∂couplingMeasure (CubicEdge d),
    X ∈ thresholdConfiguration p ⁻¹' A
  rw [ae_mem_iff_measure_eq (hA.preimage (measurable_thresholdConfiguration p)).nullMeasurableSet]
  rw [show (couplingMeasure (CubicEdge d)) Set.univ = 1 by simp]
  rw [← ENNReal.toReal_eq_one_iff, ← measureReal_def]
  unfold bernoulliBondMeasure at hAone
  rw [← couplingMeasure_map_thresholdConfiguration (ι := CubicEdge d) p] at hAone
  rw [measureReal_def] at hAone ⊢
  rw [Measure.map_apply (measurable_thresholdConfiguration p) hA] at hAone
  exact hAone

/-- Almost-sure uniqueness, transferred to the common uniform-coupling probability space. -/
theorem couplingMeasure_ae_exactlyOneInfiniteOpenCluster
    {d : ℕ} (hd : 1 ≤ d) (p : I) (htheta : 0 < theta d p) :
    ∀ᵐ X ∂couplingMeasure (CubicEdge d),
      thresholdConfiguration p X ∈ exactlyOneInfiniteOpenClusterEvent d :=
  couplingMeasure_ae_thresholdConfiguration_mem_of_measureReal_eq_one
    (measurableSet_exactlyOneInfiniteOpenClusterEvent d)
    (unique_infiniteOpenCluster_almostSure_of_theta_pos hd p htheta)

/-- A finite walk open at the target density is open at all sufficiently close densities from
the left.  This is the finite witness that turns uniqueness into left continuity. -/
theorem eventually_walkIsOpen_thresholdConfiguration_nhdsLT
    {d : ℕ} {p : I} (X : CubicEdge d → ℝ) {x y : Cubic d}
    (w : (cubicGraph d).Walk x y)
    (hopen : walkIsOpen (thresholdConfiguration p X) w) :
    ∀ᶠ q in 𝓝[<] p, walkIsOpen (thresholdConfiguration q X) w := by
  classical
  have hfin : ∀ᶠ q in 𝓝[<] p,
      ∀ e ∈ walkEdgeFinset w, e ∈ thresholdConfiguration q X := by
    rw [eventually_all_finset]
    intro e he
    have heEdges : (e : Sym2 (Cubic d)) ∈ w.edges :=
      (mem_walkEdgeFinset_iff w e).mp he
    have hep : X e < (p : ℝ) := by
      have hopen' := hopen (e : Sym2 (Cubic d)) heEdges
      simpa [edgeOpen, thresholdConfiguration] using hopen'
    have hnhds : ∀ᶠ q : I in 𝓝 p, X e < (q : ℝ) :=
      continuous_subtype_val.continuousAt.eventually
        (Ioi_mem_nhds hep)
    exact hnhds.filter_mono inf_le_left
  filter_upwards [hfin] with q hq
  intro e he
  let e' : CubicEdge d := ⟨e, w.edges_subset_edgeSet he⟩
  have he' : e' ∈ walkEdgeFinset w :=
    (mem_walkEdgeFinset_iff w e').mpr he
  have := hq e' he'
  simpa [edgeOpen, e'] using this

/-- Pointwise stabilization of the origin infinite-cluster event from the left.  At a lower
density `p₀` with an infinite cluster, uniqueness at `p₀` and `p` supplies a finite target-density
walk from the origin to the persistent lower-density infinite cluster. -/
theorem eventually_hasInfiniteOpenCluster_thresholdConfiguration_iff_nhdsLT
    {d : ℕ} {p₀ p : I} (hp₀p : p₀ < p) (X : CubicEdge d → ℝ)
    (hunique₀ : thresholdConfiguration p₀ X ∈ exactlyOneInfiniteOpenClusterEvent d)
    (huniquep : thresholdConfiguration p X ∈ exactlyOneInfiniteOpenClusterEvent d) :
    ∀ᶠ q in 𝓝[<] p,
      hasInfiniteOpenCluster d (thresholdConfiguration q X) ↔
        hasInfiniteOpenCluster d (thresholdConfiguration p X) := by
  by_cases hpInf : hasInfiniteOpenCluster d (thresholdConfiguration p X)
  · obtain ⟨x, hxInf₀, _⟩ :=
      mem_exactlyOneInfiniteOpenClusterEvent_iff.mp hunique₀
    have hxInfp : hasInfiniteOpenClusterFrom d (thresholdConfiguration p X) x :=
      isIncreasingEvent_hasInfiniteOpenClusterFrom d x
        (thresholdConfiguration_mono hp₀p.le X) hxInf₀
    obtain ⟨z, _hzInf, hzUnique⟩ :=
      mem_exactlyOneInfiniteOpenClusterEvent_iff.mp huniquep
    have hzOrigin : thresholdConfiguration p X ∈
        connectionEvent d z cubicOrigin :=
      hzUnique cubicOrigin hpInf
    have hzx : thresholdConfiguration p X ∈ connectionEvent d z x :=
      hzUnique x hxInfp
    obtain ⟨wzOrigin, hwzOrigin⟩ := hzOrigin
    obtain ⟨wzx, hwzx⟩ := hzx
    let w : (cubicGraph d).Walk cubicOrigin x := wzOrigin.reverse.append wzx
    have hwOpen : walkIsOpen (thresholdConfiguration p X) w := by
      exact walkIsOpen_append (walkIsOpen_reverse hwzOrigin) hwzx
    have hwEventually :=
      eventually_walkIsOpen_thresholdConfiguration_nhdsLT X w hwOpen
    have hp₀Eventually : ∀ᶠ q in 𝓝[<] p, p₀ < q := by
      filter_upwards [Ioo_mem_nhdsLT hp₀p] with q hq
      exact hq.1
    filter_upwards [hwEventually, hp₀Eventually] with q hwq hp₀q
    constructor
    · intro _
      exact hpInf
    · intro _
      have hxInfq : hasInfiniteOpenClusterFrom d (thresholdConfiguration q X) x :=
        isIncreasingEvent_hasInfiniteOpenClusterFrom d x
          (thresholdConfiguration_mono hp₀q.le X) hxInf₀
      exact connectionEvent_inter_subset d x cubicOrigin ⟨⟨w, hwq⟩, hxInfq⟩
  · filter_upwards [self_mem_nhdsWithin] with q hqp
    constructor
    · intro hqInf
      exact (hpInf <| isIncreasingEvent_hasInfiniteOpenCluster d
        (thresholdConfiguration_mono hqp.le X) hqInf).elim
    · exact fun h ↦ (hpInf h).elim

/-- The coupled origin-cluster indicator converges pointwise from the left on configurations
where uniqueness holds at a lower density and at the target density. -/
theorem tendsto_coupledInfiniteClusterIndicator_nhdsLT
    {d : ℕ} {p₀ p : I} (hp₀p : p₀ < p) (X : CubicEdge d → ℝ)
    (hunique₀ : thresholdConfiguration p₀ X ∈ exactlyOneInfiniteOpenClusterEvent d)
    (huniquep : thresholdConfiguration p X ∈ exactlyOneInfiniteOpenClusterEvent d) :
    Tendsto
      (fun q ↦ (coupledInfiniteClusterEvent d q).indicator (fun _ ↦ (1 : ℝ)) X)
      (𝓝[<] p)
      (𝓝 ((coupledInfiniteClusterEvent d p).indicator (fun _ ↦ (1 : ℝ)) X)) := by
  have hevent :=
    eventually_hasInfiniteOpenCluster_thresholdConfiguration_iff_nhdsLT
      hp₀p X hunique₀ huniquep
  apply Filter.EventuallyEq.tendsto
  filter_upwards [hevent] with q hq
  by_cases hqMem : hasInfiniteOpenCluster d (thresholdConfiguration q X)
  · have hpMem := hq.mp hqMem
    simp [coupledInfiniteClusterEvent, hqMem, hpMem]
  · have hpMem : ¬hasInfiniteOpenCluster d (thresholdConfiguration p X) := by
      exact fun hp ↦ hqMem (hq.mpr hp)
    simp [coupledInfiniteClusterEvent, hqMem, hpMem]

/-- **Grimmett, Lemma 8.10 (coupling form).**  If some smaller density percolates, then `θ` is
continuous from the left at the target density. -/
theorem theta_continuousWithinAt_left_of_theta_pos
    {d : ℕ} (hd : 1 ≤ d) {p₀ p : I} (hp₀p : p₀ < p)
    (htheta₀ : 0 < theta d p₀) :
    ContinuousWithinAt (theta d) (Set.Iic p) p := by
  have hthetap : 0 < theta d p :=
    htheta₀.trans_le (theta_mono d hp₀p.le)
  have haeu₀ := couplingMeasure_ae_exactlyOneInfiniteOpenCluster hd p₀ htheta₀
  have haeup := couplingMeasure_ae_exactlyOneInfiniteOpenCluster hd p hthetap
  have hlim : ∀ᵐ X ∂couplingMeasure (CubicEdge d),
      Tendsto
        (fun q ↦ (coupledInfiniteClusterEvent d q).indicator (fun _ ↦ (1 : ℝ)) X)
        (𝓝[<] p)
        (𝓝 ((coupledInfiniteClusterEvent d p).indicator (fun _ ↦ (1 : ℝ)) X)) := by
    filter_upwards [haeu₀, haeup] with X hX₀ hXp
    exact tendsto_coupledInfiniteClusterIndicator_nhdsLT hp₀p X hX₀ hXp
  have hmeas : ∀ᶠ q in 𝓝[<] p,
      AEStronglyMeasurable
        ((coupledInfiniteClusterEvent d q).indicator (fun _ ↦ (1 : ℝ)))
        (couplingMeasure (CubicEdge d)) := by
    exact Filter.Eventually.of_forall fun q ↦
      (measurable_const.indicator
        (measurableSet_coupledInfiniteClusterEvent d q)).aestronglyMeasurable
  have hbound : ∀ᶠ q in 𝓝[<] p,
      ∀ᵐ X ∂couplingMeasure (CubicEdge d),
        ‖(coupledInfiniteClusterEvent d q).indicator (fun _ ↦ (1 : ℝ)) X‖ ≤
          (1 : ℝ) := by
    exact Filter.Eventually.of_forall fun q ↦ Filter.Eventually.of_forall fun X ↦ by
      by_cases hX : X ∈ coupledInfiniteClusterEvent d q <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hX]
  have hint : Integrable (fun _ : CubicEdge d → ℝ ↦ (1 : ℝ))
      (couplingMeasure (CubicEdge d)) := integrable_const 1
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := couplingMeasure (CubicEdge d)) (fun _ ↦ (1 : ℝ))
    hmeas hbound hint hlim
  rw [← continuousWithinAt_Iio_iff_Iic]
  change Tendsto (theta d) (𝓝[<] p) (𝓝 (theta d p))
  have hintegral (q : I) :
      (∫ X, (coupledInfiniteClusterEvent d q).indicator
          (fun _ ↦ (1 : ℝ)) X ∂couplingMeasure (CubicEdge d)) = theta d q := by
    change (∫ X, (coupledInfiniteClusterEvent d q).indicator
      (1 : (CubicEdge d → ℝ) → ℝ) X ∂couplingMeasure (CubicEdge d)) = theta d q
    rw [integral_indicator_one (measurableSet_coupledInfiniteClusterEvent d q)]
    exact couplingMeasure_real_coupledInfiniteClusterEvent d q
  simpa only [hintegral] using hDCT

/-- Source-facing Lemma 8.10: above the critical probability, `θ` is left-continuous. -/
theorem theta_continuousWithinAt_left_of_criticalProbability_lt
    {d : ℕ} (hd : 2 ≤ d) {p : I}
    (hp : cubicCriticalProbability d < (p : ℝ)) :
    ContinuousWithinAt (theta d) (Set.Iic p) p := by
  let qReal : ℝ := (cubicCriticalProbability d + (p : ℝ)) / 2
  have hpc0 : 0 ≤ cubicCriticalProbability d :=
    (cubicCriticalProbability_pos_lt_one hd).1.le
  have hq0 : 0 ≤ qReal := by dsimp [qReal]; linarith [p.property.1]
  have hq1 : qReal ≤ 1 := by
    dsimp [qReal]
    linarith [cubicCriticalProbability_le_one d, p.property.2]
  let q : I := ⟨qReal, hq0, hq1⟩
  have hpcq : cubicCriticalProbability d < (q : ℝ) := by
    dsimp [q, qReal]
    linarith
  have hqp : q < p := by
    apply Subtype.coe_lt_coe.mp
    dsimp [q, qReal]
    linarith
  exact theta_continuousWithinAt_left_of_theta_pos (by omega) hqp
    (theta_pos_of_criticalProbability_lt hpcq)

/-- Grimmett Lemma 8.9: the percolation probability is continuous from the right. -/
theorem theta_continuousWithinAt_right (d : ℕ) (p : I) :
    ContinuousWithinAt (theta d) (Set.Ici p) p := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  exact theta_tendsto_nhdsGT d p

/-- **Grimmett, Theorem 8.8.**  The percolation probability is continuous at every strictly
supercritical density (including the one-sided endpoint `p = 1`). -/
theorem theta_continuousAt_of_criticalProbability_lt
    {d : ℕ} (hd : 2 ≤ d) {p : I}
    (hp : cubicCriticalProbability d < (p : ℝ)) :
    ContinuousAt (theta d) p := by
  rw [continuousAt_iff_continuous_left_right]
  exact ⟨theta_continuousWithinAt_left_of_criticalProbability_lt hd hp,
    theta_continuousWithinAt_right d p⟩

/-- Set-valued formulation of Grimmett Theorem 8.8. -/
theorem theta_continuousOn_supercritical (d : ℕ) (hd : 2 ≤ d) :
    ContinuousOn (theta d)
      {p : I | cubicCriticalProbability d < (p : ℝ)} := by
  intro p hp
  exact (theta_continuousAt_of_criticalProbability_lt hd hp).continuousWithinAt

end Percolation
