import Percolation.Critical.Radius
import Percolation.Bernoulli.BK
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Aizenman--Barsky ghost field

This file develops the independent green-vertex field used in Grimmett §5.3.  Edge states have
density `p`; green vertices have density `γ` and are independent of the edges.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal unitInterval BigOperators

abbrev GhostConfiguration (d : ℕ) := EdgeConfiguration d × Set (Cubic d)

noncomputable def ghostMeasure (d : ℕ) (p γ : I) : Measure (GhostConfiguration d) :=
  (bernoulliBondMeasure d p).prod setBer((Set.univ : Set (Cubic d)), γ)

noncomputable instance ghostMeasure_isProbabilityMeasure (d : ℕ) (p γ : I) :
    IsProbabilityMeasure (ghostMeasure d p γ) := by
  unfold ghostMeasure
  infer_instance

/-- `C ∩ G ≠ ∅`: the origin cluster contains a green vertex. -/
def ghostHitEvent (d : ℕ) : Set (GhostConfiguration d) :=
  {ξ | ∃ y : Cubic d, y ∈ cubicOpenCluster d ξ.1 ∧ y ∈ ξ.2}

/-- The complementary event that the origin cluster contains no green vertex. -/
def ghostAvoidEvent (d : ℕ) : Set (GhostConfiguration d) :=
  {ξ | Disjoint (cubicOpenCluster d ξ.1) ξ.2}

theorem ghostHitEvent_eq_iUnion (d : ℕ) :
    ghostHitEvent d = ⋃ y : Cubic d,
      Prod.fst ⁻¹' (connectionEvent d cubicOrigin y) ∩
        Prod.snd ⁻¹' {G : Set (Cubic d) | y ∈ G} := by
  ext ξ
  simp [ghostHitEvent, cubicOpenCluster, cubicOpenClusterFrom, connectionEvent]

theorem measurableSet_ghostHitEvent (d : ℕ) : MeasurableSet (ghostHitEvent d) := by
  rw [ghostHitEvent_eq_iUnion]
  apply MeasurableSet.iUnion
  intro y
  exact ((measurableSet_connectionEvent d cubicOrigin y).preimage measurable_fst).inter
    ((measurableSet_mem y).preimage measurable_snd)

theorem ghostAvoidEvent_eq_compl (d : ℕ) :
    ghostAvoidEvent d = (ghostHitEvent d)ᶜ := by
  ext ξ
  simp [ghostAvoidEvent, ghostHitEvent, Set.disjoint_left]

theorem measurableSet_ghostAvoidEvent (d : ℕ) : MeasurableSet (ghostAvoidEvent d) := by
  rw [ghostAvoidEvent_eq_compl]
  exact (measurableSet_ghostHitEvent d).compl

/-- Grimmett's `θ(p,γ)`. -/
noncomputable def ghostTheta (d : ℕ) (p γ : I) : ℝ :=
  (ghostMeasure d p γ).real (ghostHitEvent d)

theorem ghostTheta_nonneg (d : ℕ) (p γ : I) : 0 ≤ ghostTheta d p γ :=
  measureReal_nonneg

theorem ghostTheta_le_one (d : ℕ) (p γ : I) : ghostTheta d p γ ≤ 1 := by
  calc
    ghostTheta d p γ ≤ (ghostMeasure d p γ).real Set.univ :=
      measureReal_mono (Set.subset_univ _) (MeasureTheory.measure_ne_top _ _)
    _ = 1 := probReal_univ

/-- The event that the origin cluster has exactly `n` vertices.  Since `n` is finite, this
event excludes infinite clusters. -/
def finiteClusterSizeEvent (d : ℕ) (n : ℕ) : Set (EdgeConfiguration d) :=
  {ω | clusterSizeENNReal d ω = (n : ℝ≥0∞)}

theorem measurableSet_finiteClusterSizeEvent (d n : ℕ) :
    MeasurableSet (finiteClusterSizeEvent d n) := by
  exact (measurable_clusterSizeENNReal d) (measurableSet_singleton (n : ℝ≥0∞))

/-- The coefficient `Pₚ(|C|=n)` occurring in (5.42) and (5.45). -/
noncomputable def finiteClusterSizeProbability (d : ℕ) (p : I) (n : ℕ) : ℝ :=
  (bernoulliBondMeasure d p).real (finiteClusterSizeEvent d n)

theorem finiteClusterSizeProbability_nonneg (d : ℕ) (p : I) (n : ℕ) :
    0 ≤ finiteClusterSizeProbability d p n := measureReal_nonneg

theorem finiteClusterSizeProbability_le_one (d : ℕ) (p : I) (n : ℕ) :
    finiteClusterSizeProbability d p n ≤ 1 := by
  calc
    finiteClusterSizeProbability d p n ≤
        (bernoulliBondMeasure d p).real Set.univ :=
      measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := probReal_univ

theorem clusterSizeENNReal_eq_ncard_of_finite {d : ℕ} {ω : EdgeConfiguration d}
    (h : (cubicOpenCluster d ω).Finite) :
    clusterSizeENNReal d ω = ((cubicOpenCluster d ω).ncard : ℝ≥0∞) := by
  rw [clusterSizeENNReal_eq_encard, Set.ncard, h.encard_eq_coe]
  simp

/-- The event that the origin cluster is finite. -/
def finiteClusterEvent (d : ℕ) : Set (EdgeConfiguration d) :=
  {ω | (cubicOpenCluster d ω).Finite}

theorem finiteClusterEvent_eq_compl_infinite (d : ℕ) :
    finiteClusterEvent d = {ω | hasInfiniteOpenCluster d ω}ᶜ := by
  ext ω
  change (cubicOpenCluster d ω).Finite ↔ ¬(cubicOpenCluster d ω).Infinite
  simp only [Set.Infinite]
  tauto

theorem measurableSet_finiteClusterEvent (d : ℕ) : MeasurableSet (finiteClusterEvent d) := by
  rw [finiteClusterEvent_eq_compl_infinite]
  exact (measurableSet_hasInfiniteOpenCluster d).compl

theorem finiteClusterEvent_eq_iUnion_size (d : ℕ) :
    finiteClusterEvent d = ⋃ n : ℕ, finiteClusterSizeEvent d n := by
  ext ω
  constructor
  · intro hω
    let n := (cubicOpenCluster d ω).ncard
    exact Set.mem_iUnion.mpr ⟨n, clusterSizeENNReal_eq_ncard_of_finite hω⟩
  · intro hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
    by_contra hfinite
    have hinfinite : (cubicOpenCluster d ω).Infinite := hfinite
    have htop : clusterSizeENNReal d ω = ⊤ :=
      (clusterSizeENNReal_eq_top_iff d ω).mpr hinfinite
    have hsize : clusterSizeENNReal d ω = (n : ℝ≥0∞) := hn
    exact (ENNReal.natCast_ne_top n) (hsize.symm.trans htop)

theorem pairwiseDisjoint_finiteClusterSizeEvent (d : ℕ) :
    Pairwise (Function.onFun Disjoint (finiteClusterSizeEvent d)) := by
  intro m n hmn
  change Disjoint (finiteClusterSizeEvent d m) (finiteClusterSizeEvent d n)
  rw [Set.disjoint_left]
  intro ω hm hn
  apply hmn
  exact Nat.cast_injective (hm.symm.trans hn)

/-- Total mass of the finite cluster-size coefficients. -/
theorem finiteClusterProbability_eq_tsum (d : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real (finiteClusterEvent d) =
      ∑' n : ℕ, finiteClusterSizeProbability d p n := by
  rw [finiteClusterEvent_eq_iUnion_size]
  unfold finiteClusterSizeProbability
  rw [measureReal_def,
    measure_iUnion (μ := bernoulliBondMeasure d p)
      (pairwiseDisjoint_finiteClusterSizeEvent d)
      (measurableSet_finiteClusterSizeEvent d),
    ENNReal.tsum_toReal_eq]
  · rfl
  · intro n
    exact measure_ne_top (bernoulliBondMeasure d p) (finiteClusterSizeEvent d n)

theorem tsum_finiteClusterSizeProbability_eq_one_sub_theta (d : ℕ) (p : I) :
    (∑' n : ℕ, finiteClusterSizeProbability d p n) = 1 - theta d p := by
  rw [← finiteClusterProbability_eq_tsum, finiteClusterEvent_eq_compl_infinite,
    measureReal_compl (measurableSet_hasInfiniteOpenCluster d), probReal_univ]
  rfl

theorem summable_finiteClusterSizeProbability (d : ℕ) (p : I) :
    Summable (finiteClusterSizeProbability d p) := by
  apply summable_of_sum_le (finiteClusterSizeProbability_nonneg d p)
  intro s
  have hpair : Set.PairwiseDisjoint (s : Set ℕ) (finiteClusterSizeEvent d) := by
    intro m hm n hn hmn
    exact pairwiseDisjoint_finiteClusterSizeEvent d hmn
  have hmeas : ∀ n ∈ s, MeasurableSet (finiteClusterSizeEvent d n) :=
    fun n _ ↦ measurableSet_finiteClusterSizeEvent d n
  have heq := measureReal_biUnion_finset
    (μ := bernoulliBondMeasure d p) hpair hmeas
  calc
    ∑ n ∈ s, finiteClusterSizeProbability d p n =
        (bernoulliBondMeasure d p).real
          (⋃ n ∈ s, finiteClusterSizeEvent d n) := heq.symm
    _ ≤ (bernoulliBondMeasure d p).real Set.univ :=
      measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := probReal_univ

/-- Extended finite-cluster susceptibility `χᶠ(p)`. Infinite clusters contribute zero. -/
noncomputable def finiteSusceptibility (d : ℕ) (p : I) : ℝ≥0∞ :=
  by
    classical
    exact ∫⁻ ω, if (cubicOpenCluster d ω).Finite then clusterSizeENNReal d ω else 0
      ∂bernoulliBondMeasure d p

/-- Grimmett's ghost susceptibility `χ(p,γ)=E(|C|; C∩G=∅)`. -/
noncomputable def ghostSusceptibility (d : ℕ) (p γ : I) : ℝ≥0∞ :=
  by
    classical
    exact ∫⁻ ξ, if Disjoint (cubicOpenCluster d ξ.1) ξ.2
      then clusterSizeENNReal d ξ.1 else 0 ∂ghostMeasure d p γ

/-- A green field avoids a fixed finite vertex set with probability `(1-γ)^|S|`. -/
theorem setBernoulli_real_avoids_finset {d : ℕ} (S : Finset (Cubic d)) (γ : I) :
    setBer((Set.univ : Set (Cubic d)), γ).real
        {G : Set (Cubic d) | Disjoint (S : Set (Cubic d)) G} =
      (1 - (γ : ℝ)) ^ S.card :=
  setBernoulli_real_disjoint_finset_univ S γ

/-- The probability that the independent green field hits a fixed finite set. -/
theorem setBernoulli_real_hits_finset {d : ℕ} (S : Finset (Cubic d)) (γ : I) :
    setBer((Set.univ : Set (Cubic d)), γ).real
        {G : Set (Cubic d) | ¬Disjoint (S : Set (Cubic d)) G} =
      1 - (1 - (γ : ℝ)) ^ S.card := by
  let μ := setBer((Set.univ : Set (Cubic d)), γ)
  let A := {G : Set (Cubic d) | Disjoint (S : Set (Cubic d)) G}
  have hA : MeasurableSet A := by
    classical
    rw [show A = ⋂ y ∈ S, {G : Set (Cubic d) | y ∉ G} by
      ext G
      simp [A, Set.disjoint_left]]
    exact S.measurableSet_biInter fun y _ ↦ (measurableSet_mem y).compl
  have hcompl : {G : Set (Cubic d) | ¬Disjoint (S : Set (Cubic d)) G} = Aᶜ := by
    ext G
    rfl
  rw [hcompl, measureReal_compl hA, probReal_univ, setBernoulli_real_avoids_finset]

/-- Avoiding an arbitrary fixed vertex set is measurable in the green field. -/
theorem measurableSet_greenAvoids {d : ℕ} (S : Set (Cubic d)) :
    MeasurableSet {G : Set (Cubic d) | Disjoint S G} := by
  rw [show {G : Set (Cubic d) | Disjoint S G} =
      ⋂ y : S, {G : Set (Cubic d) | y.1 ∉ G} by
    ext G
    simp [Set.disjoint_left]]
  exact MeasurableSet.iInter fun y ↦ (measurableSet_mem y.1).compl

/-- The finite-set green-avoidance formula in set rather than finset form. -/
theorem setBernoulli_real_avoids_finite {d : ℕ} {S : Set (Cubic d)}
    (hS : S.Finite) (γ : I) :
    setBer((Set.univ : Set (Cubic d)), γ).real
        {G : Set (Cubic d) | Disjoint S G} =
      (1 - (γ : ℝ)) ^ S.ncard := by
  classical
  let T := hS.toFinset
  have hT : (T : Set (Cubic d)) = S := hS.coe_toFinset
  simpa [T, hT, Set.ncard_eq_toFinset_card S hS] using
    setBernoulli_real_avoids_finset T γ

/-- At positive green density, an infinite fixed vertex set is almost surely hit. -/
theorem setBernoulli_real_avoids_infinite {d : ℕ} {S : Set (Cubic d)}
    (hS : S.Infinite) (γ : I) (hγ : 0 < (γ : ℝ)) :
    setBer((Set.univ : Set (Cubic d)), γ).real
        {G : Set (Cubic d) | Disjoint S G} = 0 := by
  let μ := setBer((Set.univ : Set (Cubic d)), γ)
  let A := {G : Set (Cubic d) | Disjoint S G}
  have hq0 : 0 ≤ 1 - (γ : ℝ) := sub_nonneg.mpr γ.2.2
  have hq1 : 1 - (γ : ℝ) < 1 := by linarith
  have hlim : Filter.Tendsto (fun n : ℕ ↦ (1 - (γ : ℝ)) ^ n)
      Filter.atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  apply le_antisymm
  · apply ge_of_tendsto' hlim
    intro n
    obtain ⟨T, hTS, hcard⟩ := hS.exists_subset_card_eq n
    calc
      μ.real A ≤ μ.real {G : Set (Cubic d) | Disjoint (T : Set (Cubic d)) G} := by
        apply measureReal_mono
        · intro G hG
          exact Set.disjoint_left.mpr fun _ hxT hxG ↦
            Set.disjoint_left.mp hG (hTS hxT) hxG
        · exact measure_ne_top _ _
      _ = (1 - (γ : ℝ)) ^ T.card := setBernoulli_real_avoids_finset T γ
      _ = (1 - (γ : ℝ)) ^ n := by rw [hcard]
  · exact measureReal_nonneg

/-- Fubini disintegration of the no-green-cluster event over the bond configuration. -/
theorem ghostAvoidMeasure_eq_lintegral (d : ℕ) (p γ : I) :
    ghostMeasure d p γ (ghostAvoidEvent d) =
      ∫⁻ ω, setBer((Set.univ : Set (Cubic d)), γ)
        {G : Set (Cubic d) | Disjoint (cubicOpenCluster d ω) G}
        ∂bernoulliBondMeasure d p := by
  rw [← lintegral_indicator_one (measurableSet_ghostAvoidEvent d)]
  unfold ghostMeasure
  change (∫⁻ z : EdgeConfiguration d × Set (Cubic d),
      (ghostAvoidEvent d).indicator (fun _ ↦ (1 : ℝ≥0∞)) z
      ∂(bernoulliBondMeasure d p).prod setBer((Set.univ : Set (Cubic d)), γ)) = _
  rw [lintegral_prod _
    ((measurable_const.indicator (measurableSet_ghostAvoidEvent d)).aemeasurable)]
  apply lintegral_congr
  intro ω
  rw [← lintegral_indicator_one (measurableSet_greenAvoids (cubicOpenCluster d ω))]
  apply lintegral_congr
  intro G
  by_cases h : Disjoint (cubicOpenCluster d ω) G <;>
    simp [ghostAvoidEvent, Set.indicator, h]

/-- For a fixed edge configuration, green avoidance is the single nonzero term in the
finite-cluster-size expansion; all terms vanish on an infinite cluster. -/
theorem greenAvoidanceMeasure_eq_tsum (d : ℕ) (ω : EdgeConfiguration d) (γ : I)
    (hγ : 0 < (γ : ℝ)) :
    setBer((Set.univ : Set (Cubic d)), γ)
        {G : Set (Cubic d) | Disjoint (cubicOpenCluster d ω) G} =
      ∑' n : ℕ, (finiteClusterSizeEvent d n).indicator
        (fun _ ↦ ENNReal.ofReal ((1 - (γ : ℝ)) ^ n)) ω := by
  classical
  by_cases hC : (cubicOpenCluster d ω).Finite
  · have hsize := clusterSizeENNReal_eq_ncard_of_finite hC
    rw [← ofReal_measureReal (measure_ne_top _ _),
      setBernoulli_real_avoids_finite hC]
    let k := (cubicOpenCluster d ω).ncard
    have hevent : ∀ n : ℕ, ω ∈ finiteClusterSizeEvent d n ↔ n = k := by
      intro n
      rw [finiteClusterSizeEvent, Set.mem_setOf_eq, hsize]
      constructor
      · intro h
        exact (Nat.cast_injective h.symm)
      · rintro rfl
        rfl
    simp_rw [Set.indicator_apply, hevent]
    rw [tsum_ite_eq]
  · have hCinf : (cubicOpenCluster d ω).Infinite := hC
    rw [← ofReal_measureReal (measure_ne_top _ _),
      setBernoulli_real_avoids_infinite hCinf γ hγ]
    have htop : clusterSizeENNReal d ω = ⊤ :=
      (clusterSizeENNReal_eq_top_iff d ω).mpr hCinf
    simp [finiteClusterSizeEvent, htop]

/-- ENNReal form of the no-green-cluster series.  This is the measure-theoretic core of
Grimmett's equation (5.42). -/
theorem ghostAvoidMeasure_eq_tsum (d : ℕ) (p γ : I) (hγ : 0 < (γ : ℝ)) :
    ghostMeasure d p γ (ghostAvoidEvent d) =
      ∑' n : ℕ, ENNReal.ofReal ((1 - (γ : ℝ)) ^ n) *
        bernoulliBondMeasure d p (finiteClusterSizeEvent d n) := by
  rw [ghostAvoidMeasure_eq_lintegral]
  calc
    (∫⁻ ω, setBer((Set.univ : Set (Cubic d)), γ)
        {G : Set (Cubic d) | Disjoint (cubicOpenCluster d ω) G}
        ∂bernoulliBondMeasure d p) =
        ∫⁻ ω, ∑' n : ℕ, (finiteClusterSizeEvent d n).indicator
          (fun _ ↦ ENNReal.ofReal ((1 - (γ : ℝ)) ^ n)) ω
          ∂bernoulliBondMeasure d p := by
      apply lintegral_congr
      intro ω
      exact greenAvoidanceMeasure_eq_tsum d ω γ hγ
    _ = ∑' n : ℕ, ∫⁻ ω, (finiteClusterSizeEvent d n).indicator
          (fun _ ↦ ENNReal.ofReal ((1 - (γ : ℝ)) ^ n)) ω
          ∂bernoulliBondMeasure d p := by
      rw [lintegral_tsum]
      intro n
      exact (measurable_const.indicator (measurableSet_finiteClusterSizeEvent d n)).aemeasurable
    _ = _ := by
      apply tsum_congr
      intro n
      rw [lintegral_indicator_const (measurableSet_finiteClusterSizeEvent d n)]

theorem ghostTheta_eq_one_sub_avoid (d : ℕ) (p γ : I) :
    ghostTheta d p γ = 1 - (ghostMeasure d p γ).real (ghostAvoidEvent d) := by
  have hcompl := measureReal_compl (μ := ghostMeasure d p γ)
    (measurableSet_ghostHitEvent d)
  rw [← ghostAvoidEvent_eq_compl, probReal_univ] at hcompl
  change (ghostMeasure d p γ).real (ghostHitEvent d) = _
  rw [hcompl]
  ring

/-- Grimmett (5.42): the ghost-hit probability is the cluster-size generating series.
The sum is indexed from zero; its zero term is automatically zero because the origin cluster is
nonempty. -/
theorem ghostTheta_eq_series (d : ℕ) (p γ : I) (hγ : 0 < (γ : ℝ)) :
    ghostTheta d p γ =
      1 - ∑' n : ℕ, (1 - (γ : ℝ)) ^ n * finiteClusterSizeProbability d p n := by
  rw [ghostTheta_eq_one_sub_avoid]
  congr 1
  rw [measureReal_def, ghostAvoidMeasure_eq_tsum d p γ hγ,
    ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro n
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr γ.2.2) n)]
    rfl
  · intro n
    exact ENNReal.mul_ne_top (ENNReal.ofReal_ne_top)
      (measure_ne_top (bernoulliBondMeasure d p) (finiteClusterSizeEvent d n))

/-- Fubini disintegration of ghost susceptibility over the bond configuration. -/
theorem ghostSusceptibility_eq_lintegral (d : ℕ) (p γ : I) :
    ghostSusceptibility d p γ =
      ∫⁻ ω, clusterSizeENNReal d ω *
        setBer((Set.univ : Set (Cubic d)), γ)
          {G : Set (Cubic d) | Disjoint (cubicOpenCluster d ω) G}
        ∂bernoulliBondMeasure d p := by
  unfold ghostSusceptibility ghostMeasure
  change (∫⁻ z : EdgeConfiguration d × Set (Cubic d),
      (ghostAvoidEvent d).indicator (fun z ↦ clusterSizeENNReal d z.1) z
      ∂(bernoulliBondMeasure d p).prod setBer((Set.univ : Set (Cubic d)), γ)) = _
  · rw [lintegral_prod]
    · apply lintegral_congr
      intro ω
      rw [← lintegral_indicator_const
        (μ := setBer((Set.univ : Set (Cubic d)), γ))
        (measurableSet_greenAvoids (cubicOpenCluster d ω))
        (clusterSizeENNReal d ω)]
      apply lintegral_congr
      intro G
      by_cases h : Disjoint (cubicOpenCluster d ω) G <;>
        simp [ghostAvoidEvent, Set.indicator, h]
    · exact ((measurable_clusterSizeENNReal d).comp measurable_fst).indicator
        (measurableSet_ghostAvoidEvent d) |>.aemeasurable

/-- Fixed-configuration cluster-size-weighted green avoidance as a single-term series. -/
theorem clusterSize_mul_greenAvoidance_eq_tsum (d : ℕ) (ω : EdgeConfiguration d) (γ : I)
    (hγ : 0 < (γ : ℝ)) :
    clusterSizeENNReal d ω *
        setBer((Set.univ : Set (Cubic d)), γ)
          {G : Set (Cubic d) | Disjoint (cubicOpenCluster d ω) G} =
      ∑' n : ℕ, (finiteClusterSizeEvent d n).indicator
        (fun _ ↦ (n : ℝ≥0∞) * ENNReal.ofReal ((1 - (γ : ℝ)) ^ n)) ω := by
  classical
  by_cases hC : (cubicOpenCluster d ω).Finite
  · have hsize := clusterSizeENNReal_eq_ncard_of_finite hC
    rw [← ofReal_measureReal (measure_ne_top _ _),
      setBernoulli_real_avoids_finite hC, hsize]
    let k := (cubicOpenCluster d ω).ncard
    have hevent : ∀ n : ℕ, ω ∈ finiteClusterSizeEvent d n ↔ n = k := by
      intro n
      rw [finiteClusterSizeEvent, Set.mem_setOf_eq, hsize]
      constructor
      · intro h
        exact Nat.cast_injective h.symm
      · rintro rfl
        rfl
    simp_rw [Set.indicator_apply, hevent]
    rw [tsum_ite_eq]
  · have hCinf : (cubicOpenCluster d ω).Infinite := hC
    rw [← ofReal_measureReal (measure_ne_top _ _),
      setBernoulli_real_avoids_infinite hCinf γ hγ]
    have htop : clusterSizeENNReal d ω = ⊤ :=
      (clusterSizeENNReal_eq_top_iff d ω).mpr hCinf
    simp [finiteClusterSizeEvent, htop]

/-- Grimmett (5.45), in the extended nonnegative reals. -/
theorem ghostSusceptibility_eq_series (d : ℕ) (p γ : I) (hγ : 0 < (γ : ℝ)) :
    ghostSusceptibility d p γ =
      ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal ((1 - (γ : ℝ)) ^ n) *
        bernoulliBondMeasure d p (finiteClusterSizeEvent d n) := by
  rw [ghostSusceptibility_eq_lintegral]
  calc
    (∫⁻ ω, clusterSizeENNReal d ω *
        setBer((Set.univ : Set (Cubic d)), γ)
          {G : Set (Cubic d) | Disjoint (cubicOpenCluster d ω) G}
        ∂bernoulliBondMeasure d p) =
        ∫⁻ ω, ∑' n : ℕ, (finiteClusterSizeEvent d n).indicator
          (fun _ ↦ (n : ℝ≥0∞) * ENNReal.ofReal ((1 - (γ : ℝ)) ^ n)) ω
          ∂bernoulliBondMeasure d p := by
      apply lintegral_congr
      intro ω
      exact clusterSize_mul_greenAvoidance_eq_tsum d ω γ hγ
    _ = ∑' n : ℕ, ∫⁻ ω, (finiteClusterSizeEvent d n).indicator
          (fun _ ↦ (n : ℝ≥0∞) * ENNReal.ofReal ((1 - (γ : ℝ)) ^ n)) ω
          ∂bernoulliBondMeasure d p := by
      rw [lintegral_tsum]
      intro n
      exact (measurable_const.indicator (measurableSet_finiteClusterSizeEvent d n)).aemeasurable
    _ = _ := by
      apply tsum_congr
      intro n
      rw [lintegral_indicator_const (measurableSet_finiteClusterSizeEvent d n)]

/-! ### The differential identity (5.47) -/

/-- Real-variable extension of the right-hand side of (5.42).  It agrees with `ghostTheta`
at positive parameters in the unit interval. -/
noncomputable def ghostThetaSeries (d : ℕ) (p : I) (γ : ℝ) : ℝ :=
  1 - ∑' n : ℕ, (1 - γ) ^ n * finiteClusterSizeProbability d p n

theorem ghostTheta_eq_ghostThetaSeries (d : ℕ) (p γ : I) (hγ : 0 < (γ : ℝ)) :
    ghostTheta d p γ = ghostThetaSeries d p γ := by
  rw [ghostTheta_eq_series d p γ hγ]
  rfl

/-- Grimmett (5.43): the ghost-field generating function decreases to the ordinary
percolation probability as the green density decreases to zero. -/
theorem ghostTheta_tendsto_theta (d : ℕ) (p : I) :
    Tendsto (ghostThetaSeries d p) (nhdsWithin 0 (Set.Ioi 0)) (nhds (theta d p)) := by
  have hterm : ∀ n : ℕ, Tendsto
      (fun γ : ℝ ↦ (1 - γ) ^ n * finiteClusterSizeProbability d p n)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finiteClusterSizeProbability d p n)) := by
    intro n
    have hc : ContinuousAt
        (fun γ : ℝ ↦ (1 - γ) ^ n * finiteClusterSizeProbability d p n) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left inf_le_left
  have hbound : ∀ᶠ γ : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ n : ℕ,
      ‖(1 - γ) ^ n * finiteClusterSizeProbability d p n‖ ≤
        finiteClusterSizeProbability d p n := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
      with γ hγ0 hγ1
    simp only [Set.mem_Ioi] at hγ0
    intro n
    have hq0 : 0 ≤ 1 - γ := by linarith
    have hq1 : 1 - γ ≤ 1 := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0,
      abs_of_nonneg (finiteClusterSizeProbability_nonneg d p n)]
    exact mul_le_of_le_one_left (finiteClusterSizeProbability_nonneg d p n)
      (pow_le_one₀ hq0 hq1)
  have hseries := tendsto_tsum_of_dominated_convergence
    (summable_finiteClusterSizeProbability d p) hterm hbound
  have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    tendsto_const_nhds
  have hsub := hone.sub hseries
  change Tendsto
    (fun γ : ℝ ↦ 1 - ∑' n : ℕ,
      (1 - γ) ^ n * finiteClusterSizeProbability d p n)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (1 - ∑' n : ℕ, finiteClusterSizeProbability d p n)) at hsub
  rw [tsum_finiteClusterSizeProbability_eq_one_sub_theta] at hsub
  have heq : 1 - (1 - theta d p) = theta d p := by ring
  rw [heq] at hsub
  change Tendsto (ghostThetaSeries d p) (nhdsWithin 0 (Set.Ioi 0))
    (nhds (theta d p)) at hsub
  exact hsub

theorem ghostThetaSeries_term_hasDerivAt (d : ℕ) (p : I) (n : ℕ) (γ : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ (1 - x) ^ n * finiteClusterSizeProbability d p n)
      (-(n : ℝ) * (1 - γ) ^ (n - 1) * finiteClusterSizeProbability d p n) γ := by
  convert (((hasDerivAt_id γ).const_sub (1 : ℝ)).pow n).mul_const
    (finiteClusterSizeProbability d p n) using 1
  simp only [Function.id_def]
  ring

/-- Termwise differentiation of the cluster-size generating series at every interior green
density. -/
theorem ghostThetaSeries_hasDerivAt (d : ℕ) (p : I) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    HasDerivAt (ghostThetaSeries d p)
      (∑' n : ℕ, (n : ℝ) * (1 - γ) ^ (n - 1) *
        finiteClusterSizeProbability d p n) γ := by
  let r : ℝ := 1 - γ / 2
  let u : ℕ → ℝ := fun n ↦ (n : ℝ) * r ^ (n - 1)
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hu : Summable u := by
    apply (summable_nat_add_iff 1).mp
    have hnat := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
    have hgeom := summable_geometric_of_norm_lt_one hrnorm
    simpa [u, pow_one, add_mul] using hnat.add hgeom
  have hγmem : γ ∈ Set.Ioo (γ / 2) 1 := by constructor <;> linarith
  have hbase : Summable (fun n : ℕ ↦
      (1 - γ) ^ n * finiteClusterSizeProbability d p n) := by
    have hq0 : 0 ≤ 1 - γ := by linarith
    have hqnorm : ‖1 - γ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hq0]
      linarith
    apply (summable_geometric_of_norm_lt_one hqnorm).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0,
      abs_of_nonneg (finiteClusterSizeProbability_nonneg d p n)]
    exact mul_le_of_le_one_right (pow_nonneg hq0 n)
      (finiteClusterSizeProbability_le_one d p n)
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (γ / 2) 1 →
      ‖-(n : ℝ) * (1 - y) ^ (n - 1) * finiteClusterSizeProbability d p n‖ ≤ u n := by
    intro n y hy
    have hyq0 : 0 ≤ 1 - y := by linarith [hy.2]
    have hyqr : 1 - y ≤ r := by dsimp [r]; linarith [hy.1]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n), abs_pow,
      abs_of_nonneg hyq0,
      abs_of_nonneg (finiteClusterSizeProbability_nonneg d p n)]
    dsimp [u]
    calc
      (n : ℝ) * (1 - y) ^ (n - 1) * finiteClusterSizeProbability d p n ≤
          (n : ℝ) * (1 - y) ^ (n - 1) * 1 :=
        mul_le_mul_of_nonneg_left (finiteClusterSizeProbability_le_one d p n)
          (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hyq0 _))
      _ = (n : ℝ) * (1 - y) ^ (n - 1) := by ring
      _ ≤ (n : ℝ) * r ^ (n - 1) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hyq0 hyqr (n - 1)) (Nat.cast_nonneg n)
  have hsum := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ ↦ ghostThetaSeries_term_hasDerivAt d p n y) hbound hγmem hbase hγmem
  have htheta := hsum.const_sub (1 : ℝ)
  have hderiv :
      -(∑' n : ℕ, -(n : ℝ) * (1 - γ) ^ (n - 1) *
          finiteClusterSizeProbability d p n) =
        ∑' n : ℕ, (n : ℝ) * (1 - γ) ^ (n - 1) *
          finiteClusterSizeProbability d p n := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    ring
  rw [hderiv] at htheta
  exact htheta

theorem ghostSusceptibility_toReal_eq_series (d : ℕ) (p γ : I)
    (hγ : 0 < (γ : ℝ)) :
    (ghostSusceptibility d p γ).toReal =
      ∑' n : ℕ, (n : ℝ) * (1 - (γ : ℝ)) ^ n *
        finiteClusterSizeProbability d p n := by
  rw [ghostSusceptibility_eq_series d p γ hγ, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro n
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rw [ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr γ.2.2) n)]
    rfl
  · intro n
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top)
      (measure_ne_top (bernoulliBondMeasure d p) (finiteClusterSizeEvent d n))

/-- Grimmett (5.47): `χ(p,γ) = (1-γ) ∂γ θ(p,γ)` for `0 < γ < 1`.
The derivative is taken on the real-variable series extension, which agrees with the probabilistic
`ghostTheta` throughout the open unit interval. -/
theorem ghostSusceptibility_eq_deriv (d : ℕ) (p γ : I)
    (hγ0 : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) :
    (ghostSusceptibility d p γ).toReal =
      (1 - (γ : ℝ)) * deriv (ghostThetaSeries d p) (γ : ℝ) := by
  have hderiv := ghostThetaSeries_hasDerivAt d p hγ0 hγ1
  rw [hderiv.deriv, ghostSusceptibility_toReal_eq_series d p γ hγ0,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  cases n with
  | zero => simp
  | succ n =>
      rw [Nat.succ_sub_one, pow_succ]
      ring

end Percolation
