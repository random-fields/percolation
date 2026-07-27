import Percolation.Critical.BondToSiteCritical
import Percolation.Critical.SiteSymmetry
import Percolation.Extensions.ContinuumApproximation
import Percolation.Planar.Peierls

/-!
# Site-percolation law of the continuum cube approximation

Grimmett's equation (12.38) is useful only after the whole occupied-cube field, rather than one
coordinate, has been identified.  This file performs that passage and compares the resulting
finite-range site model with ordinary cubic site percolation.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set SimpleGraph
open scoped ENNReal NNReal unitInterval

/-- Enlarging the underlying graph can only enlarge a site-open cluster. -/
theorem siteOpenCluster_mono_graph {V : Type*} {G H : SimpleGraph V}
    (hGH : G ≤ H) (eta : Set V) (x : V) :
    siteOpenCluster G eta x ⊆ siteOpenCluster H eta x := by
  rintro y ⟨w, hw⟩
  induction w with
  | nil =>
      exact ⟨.nil, by simpa using hw⟩
  | @cons u v y huv w ih =>
      have htail : ∀ z ∈ w.support, z ∈ eta := by
        intro z hz
        exact hw z (by simp [hz])
      obtain ⟨q, hq⟩ := ih htail
      refine ⟨SimpleGraph.Walk.cons (hGH huv) q, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hw _ (by simp)
      · exact hq z hz

/-- Enlarging the underlying graph preserves existence of an infinite site cluster. -/
theorem hasInfiniteSiteCluster_mono_graph {V : Type*} {G H : SimpleGraph V}
    (hGH : G ≤ H) {eta : Set V} :
    hasInfiniteSiteCluster G eta → hasInfiniteSiteCluster H eta := by
  rintro ⟨x, hx⟩
  exact ⟨x, hx.mono (siteOpenCluster_mono_graph hGH eta x)⟩

/-- Site percolation probability is monotone under addition of graph edges. -/
theorem siteTheta_mono_graph {V : Type*} [Countable V] {G H : SimpleGraph V}
    (hGH : G ≤ H) (p : I) :
    siteTheta G p ≤ siteTheta H p := by
  unfold siteTheta
  exact measureReal_mono fun eta heta ↦ hasInfiniteSiteCluster_mono_graph hGH heta

/-- Adding graph edges can only lower the site-percolation critical probability. -/
theorem siteCriticalProbability_antitone_graph
    {V : Type*} [Countable V] {G H : SimpleGraph V} (hGH : G ≤ H) :
    siteCriticalProbability H ≤ siteCriticalProbability G := by
  rw [siteCriticalProbability, siteCriticalProbability]
  apply csSup_le
  · exact ⟨0, ⟨(0 : I), siteTheta_zero H, rfl⟩⟩
  · rintro q ⟨p, hp, rfl⟩
    apply le_csSup
    · exact ⟨1, by
        rintro r ⟨s, _hs, rfl⟩
        exact s.2.2⟩
    · refine ⟨p, ?_, rfl⟩
      exact le_antisymm ((siteTheta_mono_graph hGH p).trans_eq hp) measureReal_nonneg

/-- Infinite occupied cluster event for the Poisson cube-count discretization. -/
def continuumApproximationPercolatesEvent (d n : ℕ) :
    Set (PoissonCubeConfiguration d) :=
  {N | hasInfiniteSiteCluster (continuumApproximationGraph d n) (continuumOccupiedSites N)}

theorem measurableSet_continuumApproximationPercolatesEvent (d n : ℕ) :
    MeasurableSet (continuumApproximationPercolatesEvent d n) := by
  exact (measurableSet_hasInfiniteSiteCluster (continuumApproximationGraph d n)).preimage
    measurable_continuumOccupiedSites

/-- Probability that the Poisson cube-count approximation has an infinite occupied cluster. -/
noncomputable def continuumApproximationTheta
    (d : ℕ) (intensity : ℝ≥0) (n : ℕ) : ℝ :=
  (poissonCubeMeasure d intensity n).real (continuumApproximationPercolatesEvent d n)

/-- Exact probabilistic content of (12.38): the cube approximation is iid site percolation on
`L_n` with density `1 - exp(-lambda / n^d)`. -/
theorem continuumApproximationTheta_eq_siteTheta
    (d : ℕ) (intensity : ℝ≥0) (n : ℕ) :
    continuumApproximationTheta d intensity n =
      siteTheta (continuumApproximationGraph d n)
        (continuumCubeDensity d intensity n) := by
  unfold continuumApproximationTheta continuumApproximationPercolatesEvent siteTheta
  have hmap := poissonCubeMeasure_map_continuumOccupiedSites d intensity n
  have hcongr := congrArg (fun mu : Measure (Set (Cubic d)) ↦
      mu {eta | hasInfiniteSiteCluster (continuumApproximationGraph d n) eta}) hmap
  change (Measure.map continuumOccupiedSites (poissonCubeMeasure d intensity n))
      {eta | hasInfiniteSiteCluster (continuumApproximationGraph d n) eta} = _ at hcongr
  rw [Measure.map_apply measurable_continuumOccupiedSites
    (measurableSet_hasInfiniteSiteCluster (continuumApproximationGraph d n))] at hcongr
  exact congrArg ENNReal.toReal hcongr

/-- Since `L_n` contains every nearest-neighbour cubic edge, its site-percolation probability is
at least the ordinary cubic site-percolation probability. -/
theorem siteTheta_cubic_le_continuumApproximationTheta
    {d n : ℕ} (hn : 0 < n) (intensity : ℝ≥0) :
    siteTheta (cubicGraph d) (continuumCubeDensity d intensity n) ≤
      continuumApproximationTheta d intensity n := by
  rw [continuumApproximationTheta_eq_siteTheta]
  exact siteTheta_mono_graph (cubicGraph_le_continuumApproximationGraph hn) _

/-- Any mesh density above the cubic site threshold percolates in Grimmett's approximation. -/
theorem continuumApproximationTheta_pos_of_cubicSiteCritical_lt
    {d n : ℕ} (hn : 0 < n) (intensity : ℝ≥0)
    (hcrit : siteCriticalProbability (cubicGraph d) <
      (continuumCubeDensity d intensity n : ℝ)) :
    0 < continuumApproximationTheta d intensity n := by
  exact (siteTheta_pos_of_criticalProbability_lt hcrit).trans_le
    (siteTheta_cubic_le_continuumApproximationTheta hn intensity)

/-- The ordinary cubic site threshold is strictly below one in dimensions at least two. -/
theorem cubicSiteCriticalProbability_lt_one {d : ℕ} (hd : 2 ≤ d) :
    siteCriticalProbability (cubicGraph d) < 1 := by
  let root : (Set.univ : Set (Cubic d)) := ⟨cubicOrigin, Set.mem_univ _⟩
  have hregion :
      siteCriticalProbability (cubicRegionGraph d Set.univ) < 1 :=
    siteCriticalProbability_lt_one_of_regionCriticalProbability_lt_one root hd
      (cubicRegionGraph_univ_connected d) (by
        rw [regionCriticalProbability_univ]
        exact (cubicCriticalProbability_pos_lt_one hd).2)
  have hiso := siteCriticalProbability_graphIso ((cubicGraph d).induceUnivIso)
  exact hiso ▸ hregion

/-- Every positive-mesh approximation lattice has site threshold strictly below one in
dimension at least two. -/
theorem continuumApproximation_siteCriticalProbability_lt_one
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    siteCriticalProbability (continuumApproximationGraph d n) < 1 :=
  (siteCriticalProbability_antitone_graph
    (cubicGraph_le_continuumApproximationGraph hn)).trans_lt
      (cubicSiteCriticalProbability_lt_one hd)

/-- Scaling the intensity by the number of mesh cubes per unit volume makes the one-cube
Poisson rate equal to the chosen scalar. -/
@[simp]
theorem continuumCubeRate_nat_scaled {d n k : ℕ} (hn : 0 < n) :
    continuumCubeRate d ((k : ℝ≥0) * (n : ℝ≥0) ^ d) n = k := by
  unfold continuumCubeRate
  rw [mul_div_cancel_right₀]
  positivity

/-- For every fixed positive mesh in dimension at least two, some finite Poisson intensity
percolates in the occupied-cube approximation. -/
theorem exists_continuumApproximationTheta_pos
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    ∃ intensity : ℝ≥0, 0 < continuumApproximationTheta d intensity n := by
  let c := siteCriticalProbability (cubicGraph d)
  have hc1 : c < 1 := cubicSiteCriticalProbability_lt_one hd
  have hgap : 0 < 1 - c := sub_pos.mpr hc1
  have hlim : Filter.Tendsto (fun k : ℕ ↦ Real.exp (-(k : ℝ)))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ k : ℕ in Filter.atTop, Real.exp (-(k : ℝ)) < 1 - c :=
    hlim.eventually (Iio_mem_nhds hgap)
  obtain ⟨k, hk⟩ := hev.exists
  let intensity : ℝ≥0 := (k : ℝ≥0) * (n : ℝ≥0) ^ d
  refine ⟨intensity, continuumApproximationTheta_pos_of_cubicSiteCritical_lt hn intensity ?_⟩
  dsimp [intensity]
  rw [continuumCubeRate_nat_scaled hn]
  change siteCriticalProbability (cubicGraph d) < 1 - Real.exp (-(k : ℝ))
  dsimp [c] at hk
  linarith

end Percolation
