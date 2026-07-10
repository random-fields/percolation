import Percolation.Critical.ConcreteAnimals
import Percolation.Critical.GhostField
import Percolation.Critical.ClusterDensityDerivative

/-!
# Concrete cluster-size and animal series

This file supplies the missing converse to the cluster-cylinder construction: every finite origin
cluster determines its canonical cubic bond animal.  Consequently the concrete animal coefficients
are an exact expansion of the finite cluster-size probabilities, rather than merely upper bounds.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal unitInterval

noncomputable section

theorem iUnion_cubicBondAnimal_clusterCylinder (d n : ℕ) :
    (⋃ A : CubicBondAnimal d n, A.clusterCylinder) = finiteClusterSizeEvent d n := by
  ext ω
  constructor
  · intro hω
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hω
    have hcluster := A.cubicOpenCluster_eq_vertices_of_mem_clusterCylinder hA
    have hfinite : (cubicOpenCluster d ω).Finite := by
      rw [hcluster]
      exact A.vertices.finite_toSet
    change clusterSizeENNReal d ω = (n : ℝ≥0∞)
    rw [clusterSizeENNReal_eq_ncard_of_finite hfinite, hcluster]
    simp [A.vertices_card]
  · intro hω
    have hfinite : (cubicOpenCluster d ω).Finite := by
      by_contra h
      have htop := (clusterSizeENNReal_eq_top_iff d ω).mpr h
      exact (ENNReal.natCast_ne_top n) (hω.symm.trans htop)
    have hncard : (cubicOpenCluster d ω).ncard = n := by
      have hsize := clusterSizeENNReal_eq_ncard_of_finite hfinite
      rw [hω] at hsize
      exact_mod_cast hsize.symm
    exact Set.mem_iUnion.mpr
      ⟨CubicBondAnimal.ofFiniteCluster hfinite hncard,
        CubicBondAnimal.ofFiniteCluster_mem_clusterCylinder hfinite hncard⟩

/-- Exact finite-volume animal decomposition before grouping by `(m,b)`. -/
theorem finiteClusterSizeProbability_eq_sum_animals (d n : ℕ) (p : I) :
    finiteClusterSizeProbability d p n =
      ∑ A : CubicBondAnimal d n,
        (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card := by
  let F : CubicBondAnimal d n → Set (EdgeConfiguration d) :=
    fun A ↦ A.clusterCylinder
  have hpair : Pairwise (Function.onFun Disjoint F) :=
    CubicBondAnimal.clusterCylinder_pairwiseDisjoint
  have hmeas : ∀ A, MeasurableSet (F A) :=
    fun A ↦ A.measurableSet_clusterCylinder
  have hunion := measureReal_iUnion_fintype
    (μ := bernoulliBondMeasure d p) hpair hmeas
  rw [show (⋃ A, F A) = finiteClusterSizeEvent d n by
    exact iUnion_cubicBondAnimal_clusterCylinder d n] at hunion
  change (bernoulliBondMeasure d p).real (finiteClusterSizeEvent d n) = _
  rw [hunion]
  apply Finset.sum_congr rfl
  intro A _hA
  exact A.bernoulliBondMeasure_real_clusterCylinder p

/-- Grouping the exact animal sum by occupied and boundary edge counts gives the concrete
coefficient expansion (4.17)/(5.75). -/
theorem finiteClusterSizeProbability_eq_sum_cubicAnimalCount
    {d : ℕ} (hd : 0 < d) (n : ℕ) (p : I) :
    finiteClusterSizeProbability d p n =
      ∑ z ∈ animalParameterPairs d n,
        (cubicAnimalCount d n z.1 z.2 : ℝ) *
          (p : ℝ) ^ z.1 * (1 - (p : ℝ)) ^ z.2 := by
  classical
  let g : CubicBondAnimal d n → ℕ × ℕ := fun A ↦ (A.edges.card, A.boundary.card)
  let f : CubicBondAnimal d n → ℝ := fun A ↦
    (p : ℝ) ^ A.edges.card * (1 - (p : ℝ)) ^ A.boundary.card
  have hmaps : ∀ A ∈ (Finset.univ : Finset (CubicBondAnimal d n)),
      g A ∈ animalParameterPairs d n := by
    intro A _hA
    change (A.edges.card, A.boundary.card) ∈
      (Finset.Icc (n - 1) (d * n)).product (Finset.Icc 1 (2 * d * n))
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨A.edges_card_lower, A.edges_card_upper⟩,
        Finset.mem_Icc.mpr ⟨A.boundary_card_pos hd, A.boundary_card_le⟩⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps f
  rw [finiteClusterSizeProbability_eq_sum_animals d n p]
  change (∑ A : CubicBondAnimal d n, f A) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro z hz
  have hconst : ∀ A ∈ (Finset.univ.filter fun A : CubicBondAnimal d n ↦ g A = z),
      f A = (p : ℝ) ^ z.1 * (1 - (p : ℝ)) ^ z.2 := by
    intro A hA
    have hAz := Finset.mem_filter.mp hA |>.2
    have hm := congrArg Prod.fst hAz
    have hb := congrArg Prod.snd hAz
    simp only [g] at hm hb
    simp [f, hm, hb]
  have hfiberCard : (Finset.univ.filter fun A : CubicBondAnimal d n ↦ g A = z).card =
      cubicAnimalCount d n z.1 z.2 := by
    rw [cubicAnimalCount, ← Fintype.card_subtype (fun A : CubicBondAnimal d n ↦ g A = z)]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivProp
    funext A
    apply propext
    exact Prod.ext_iff
  rw [Finset.sum_eq_card_nsmul hconst, nsmul_eq_mul, hfiberCard]
  ring

def reciprocalClusterSizeTerm (d n : ℕ) : EdgeConfiguration d → ℝ :=
  (finiteClusterSizeEvent d n).indicator fun _ ↦ 1 / (n : ℝ)

theorem tsum_reciprocalClusterSizeTerm (d : ℕ) (ω : EdgeConfiguration d) :
    ∑' n : ℕ, reciprocalClusterSizeTerm d n ω =
      1 / ((cubicOpenCluster d ω).ncard : ℝ) := by
  by_cases hfinite : (cubicOpenCluster d ω).Finite
  · let k := (cubicOpenCluster d ω).ncard
    have hk : 0 < k := by
      rw [Set.ncard_pos hfinite]
      exact ⟨cubicOrigin, ⟨SimpleGraph.Walk.nil, by intro e he; cases he⟩⟩
    have hterm : ∀ n : ℕ, reciprocalClusterSizeTerm d n ω =
        if n = k then 1 / (k : ℝ) else 0 := by
      intro n
      by_cases hnk : n = k
      · subst n
        have hmem : ω ∈ finiteClusterSizeEvent d k :=
          clusterSizeENNReal_eq_ncard_of_finite hfinite
        simp [reciprocalClusterSizeTerm, hmem]
      · have hnot : ω ∉ finiteClusterSizeEvent d n := by
          intro hmem
          apply hnk
          have hsize := clusterSizeENNReal_eq_ncard_of_finite hfinite
          rw [hmem] at hsize
          exact_mod_cast hsize
        simp [reciprocalClusterSizeTerm, hnot, hnk]
    simp_rw [hterm]
    simp [k]
  · have hinfinite : (cubicOpenCluster d ω).Infinite := hfinite
    have hncard : (cubicOpenCluster d ω).ncard = 0 := hinfinite.ncard
    have hterm : ∀ n : ℕ, reciprocalClusterSizeTerm d n ω = 0 := by
      intro n
      rw [reciprocalClusterSizeTerm, Set.indicator_of_notMem]
      intro hmem
      have htop := (clusterSizeENNReal_eq_top_iff d ω).mpr hinfinite
      exact (ENNReal.natCast_ne_top n) (hmem.symm.trans htop)
    simp [hterm, hncard]

theorem integral_reciprocalClusterSizeTerm (d n : ℕ) (p : I) :
    ∫ ω, reciprocalClusterSizeTerm d n ω ∂bernoulliBondMeasure d p =
      (1 / (n : ℝ)) * finiteClusterSizeProbability d p n := by
  rw [reciprocalClusterSizeTerm,
    integral_indicator_const (1 / (n : ℝ)) (measurableSet_finiteClusterSizeEvent d n),
    smul_eq_mul]
  unfold finiteClusterSizeProbability
  ring

/-- Equation (4.18) before replacing `P_p(|C|=n)` by its concrete animal coefficient sum. -/
theorem openClustersPerVertex_eq_tsum_finiteClusterSizeProbability (d : ℕ) (p : I) :
    openClustersPerVertex d p =
      ∑' n : ℕ, (1 / (n : ℝ)) * finiteClusterSizeProbability d p n := by
  let μ := bernoulliBondMeasure d p
  let F : ℕ → EdgeConfiguration d → ℝ := reciprocalClusterSizeTerm d
  have hFint : ∀ n, Integrable (F n) μ := by
    intro n
    exact (integrable_const (1 / (n : ℝ))).indicator
      (measurableSet_finiteClusterSizeEvent d n)
  have hcoeffNonneg : ∀ n : ℕ,
      0 ≤ (1 / (n : ℝ)) * finiteClusterSizeProbability d p n := by
    intro n
    exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n))
      (finiteClusterSizeProbability_nonneg d p n)
  have hcoeffLe : ∀ n : ℕ,
      (1 / (n : ℝ)) * finiteClusterSizeProbability d p n ≤
        finiteClusterSizeProbability d p n := by
    intro n
    by_cases hn : n = 0
    · simp [hn, finiteClusterSizeProbability_nonneg d p 0]
    · apply mul_le_of_le_one_left (finiteClusterSizeProbability_nonneg d p n)
      have hncast : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hncast
  have hprobSummable : Summable (finiteClusterSizeProbability d p) :=
    summable_finiteClusterSizeProbability d p
  have hcoeffSummable : Summable fun n : ℕ ↦
      (1 / (n : ℝ)) * finiteClusterSizeProbability d p n :=
    hprobSummable.of_nonneg_of_le hcoeffNonneg hcoeffLe
  have hnorm : ∀ n : ℕ,
      ∫ ω, ‖F n ω‖ ∂μ =
        (1 / (n : ℝ)) * finiteClusterSizeProbability d p n := by
    intro n
    have hnonneg : ∀ ω, 0 ≤ F n ω := by
      intro ω
      exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
    rw [show (fun ω ↦ ‖F n ω‖) = F n by
      funext ω
      exact Real.norm_of_nonneg (hnonneg ω)]
    exact integral_reciprocalClusterSizeTerm d n p
  have hsumNorm : Summable fun n : ℕ ↦ ∫ ω, ‖F n ω‖ ∂μ := by
    simpa only [hnorm] using hcoeffSummable
  rw [openClustersPerVertex_eq_integral_inv_ncard]
  rw [show (fun ω : EdgeConfiguration d ↦ 1 / ((cubicOpenCluster d ω).ncard : ℝ)) =
      fun ω ↦ ∑' n : ℕ, F n ω by
    funext ω
    exact (tsum_reciprocalClusterSizeTerm d ω).symm]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsumNorm]
  apply tsum_congr
  intro n
  exact integral_reciprocalClusterSizeTerm d n p

end

end Percolation
