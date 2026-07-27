import Percolation.Critical.ConcreteAnimals
import Percolation.Critical.GhostField
import Percolation.Critical.ClusterDensityDerivative
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

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

/-! ### The concrete level series and its formal derivative -/

/-- The contribution of clusters with exactly `n` vertices to the concrete animal expansion
of the number of open clusters per vertex.  Grouping by `n` is important: the cancellations in
Grimmett's proof of Theorem 4.31 occur inside each such finite sum. -/
def concreteClusterDensityLevel (d n : ℕ) (p : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ z ∈ animalParameterPairs d n,
      (cubicAnimalCount d n z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2

/-- The term-by-term derivative of `concreteClusterDensityLevel`, corresponding to the
`n`-th group in Grimmett's equation (4.32). -/
def concreteClusterDensityLevelDerivative (d n : ℕ) (p : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ z ∈ animalParameterPairs d n,
      (cubicAnimalCount d n z.1 z.2 : ℝ) *
        ((z.1 : ℝ) * p ^ (z.1 - 1) * (1 - p) ^ z.2 -
          (z.2 : ℝ) * p ^ z.1 * (1 - p) ^ (z.2 - 1))

def concreteAnimalWeight (d n : ℕ) (p : ℝ) (z : ℕ × ℕ) : ℝ :=
  (cubicAnimalCount d n z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2

def animalDerivativeScore (p : ℝ) (z : ℕ × ℕ) : ℝ :=
  (z.1 : ℝ) / p - (z.2 : ℝ) / (1 - p)

/-- The concrete lattice-animal series for the open-cluster density, grouped by cluster size. -/
def concreteClusterDensitySeries (d : ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, concreteClusterDensityLevel d n p

/-- The concrete derivative series in equation (4.32), grouped by cluster size. -/
def concreteClusterDensityDerivativeSeries (d : ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, concreteClusterDensityLevelDerivative d n p

theorem concreteClusterDensityLevel_hasDerivAt (d n : ℕ) (p : ℝ) :
    HasDerivAt (concreteClusterDensityLevel d n)
      (concreteClusterDensityLevelDerivative d n p) p := by
  unfold concreteClusterDensityLevel concreteClusterDensityLevelDerivative
  have hsum : HasDerivAt
      (fun y : ℝ ↦ ∑ z ∈ animalParameterPairs d n,
        (cubicAnimalCount d n z.1 z.2 : ℝ) * y ^ z.1 * (1 - y) ^ z.2)
      (∑ z ∈ animalParameterPairs d n,
        (cubicAnimalCount d n z.1 z.2 : ℝ) *
          ((z.1 : ℝ) * p ^ (z.1 - 1) * (1 - p) ^ z.2 -
            (z.2 : ℝ) * p ^ z.1 * (1 - p) ^ (z.2 - 1))) p := by
    apply HasDerivAt.fun_sum
    intro z _hz
    have hp := (hasDerivAt_id p).pow z.1
    have hq := ((hasDerivAt_id p).neg.add_const 1).pow z.2
    convert (hp.mul hq).const_mul (cubicAnimalCount d n z.1 z.2 : ℝ) using 1 <;>
      simp only [Function.id_def, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply] <;> ring_nf
  exact hsum.const_mul (1 / (n : ℝ))

theorem concreteClusterDensityLevel_eq_probability
    {d : ℕ} (hd : 0 < d) (n : ℕ) (p : I) :
    concreteClusterDensityLevel d n p =
      (1 / (n : ℝ)) * finiteClusterSizeProbability d p n := by
  rw [concreteClusterDensityLevel,
    finiteClusterSizeProbability_eq_sum_cubicAnimalCount hd n p]

theorem natCast_mul_pow_pred_eq_pow_mul_div (m : ℕ) {p : ℝ} (hp : p ≠ 0) :
    (m : ℝ) * p ^ (m - 1) = p ^ m * ((m : ℝ) / p) := by
  cases m with
  | zero => simp
  | succ k =>
      rw [Nat.succ_sub_one, pow_succ]
      field_simp

theorem concreteClusterDensityLevelDerivative_eq_ratio
    {d n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    concreteClusterDensityLevelDerivative d n p =
      (1 / (n : ℝ)) *
        ∑ z ∈ animalParameterPairs d n,
          concreteAnimalWeight d n p z * animalDerivativeScore p z := by
  have hp : p ≠ 0 := ne_of_gt hp0
  have hq : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  unfold concreteClusterDensityLevelDerivative
  unfold concreteAnimalWeight animalDerivativeScore
  congr 1
  apply Finset.sum_congr rfl
  intro z _hz
  rw [natCast_mul_pow_pred_eq_pow_mul_div z.1 hp]
  have hb := natCast_mul_pow_pred_eq_pow_mul_div z.2 hq
  calc
    (cubicAnimalCount d n z.1 z.2 : ℝ) *
          (p ^ z.1 * ((z.1 : ℝ) / p) * (1 - p) ^ z.2 -
            (z.2 : ℝ) * p ^ z.1 * (1 - p) ^ (z.2 - 1)) =
        (cubicAnimalCount d n z.1 z.2 : ℝ) *
          (p ^ z.1 * ((z.1 : ℝ) / p) * (1 - p) ^ z.2 -
            p ^ z.1 * ((1 - p) ^ z.2 * ((z.2 : ℝ) / (1 - p)))) := by
      rw [← hb]
      ring
    _ = ((cubicAnimalCount d n z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2) *
          ((z.1 : ℝ) / p - (z.2 : ℝ) / (1 - p)) := by ring

theorem sum_finiteClusterSizeProbability_le_one
    (d : ℕ) (p : I) (s : Finset ℕ) :
    ∑ n ∈ s, finiteClusterSizeProbability d p n ≤ 1 := by
  calc
    ∑ n ∈ s, finiteClusterSizeProbability d p n ≤
        ∑' n : ℕ, finiteClusterSizeProbability d p n :=
      (summable_finiteClusterSizeProbability d p).sum_le_tsum s
        (fun n _hn ↦ finiteClusterSizeProbability_nonneg d p n)
    _ = 1 - theta d p := tsum_finiteClusterSizeProbability_eq_one_sub_theta d p
    _ ≤ 1 := sub_le_self _ measureReal_nonneg

theorem concreteAnimalWeight_nonneg {d n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℕ × ℕ) :
    0 ≤ concreteAnimalWeight d n p z := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- The cancellation estimate behind equations (4.33)–(4.35): after grouping animals with the
same vertex count, the derivative is bounded by a small multiple of the entire level mass plus
the large-deviation mass. -/
theorem norm_concreteClusterDensityLevelDerivative_le_split
    {d n : ℕ} {p₁ p p₂ x : ℝ} (hd : 0 < d) (hn : 2 ≤ n)
    (hp₁0 : 0 < p₁) (hp₁p : p₁ ≤ p) (hpp₂ : p ≤ p₂) (hp₂1 : p₂ < 1)
    (hx0 : 0 < x) :
    ‖concreteClusterDensityLevelDerivative d n p‖ ≤
      (d : ℝ) * x *
          ∑ z ∈ animalParameterPairs d n, concreteAnimalWeight d n p z +
        ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) *
          ∑ z ∈ exceptionalAnimalPairs d n p x, concreteAnimalWeight d n p z := by
  have hp0 : 0 < p := hp₁0.trans_le hp₁p
  have hp1 : p < 1 := hpp₂.trans_lt hp₂1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hp₁nonneg : 0 ≤ p₁ := hp₁0.le
  have hq₂ : 0 < 1 - p₂ := sub_pos.mpr hp₂1
  let A := animalParameterPairs d n
  let E := exceptionalAnimalPairs d n p x
  let N := A.filter fun z ↦
    ¬((d : ℝ) * x * n < |animalDerivativeScore p z|)
  let W := concreteAnimalWeight d n p
  let R := animalDerivativeScore p
  have hE : E = A.filter fun z ↦ (d : ℝ) * x * n < |R z| := by
    rfl
  have hsplit : ∑ z ∈ A, W z * R z =
      (∑ z ∈ E, W z * R z) + ∑ z ∈ N, W z * R z := by
    rw [hE]
    simpa [N] using
      (Finset.sum_filter_add_sum_filter_not A
        (fun z ↦ (d : ℝ) * x * n < |R z|) (fun z ↦ W z * R z)).symm
  have hnormal : ‖∑ z ∈ N, W z * R z‖ ≤
      ((d : ℝ) * x * n) * ∑ z ∈ N, W z := by
    calc
      ‖∑ z ∈ N, W z * R z‖ ≤ ∑ z ∈ N, ‖W z * R z‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ N, ((d : ℝ) * x * n) * W z := by
        apply Finset.sum_le_sum
        intro z hz
        have hzN := (Finset.mem_filter.mp hz).2
        have hscore : |R z| ≤ (d : ℝ) * x * n := le_of_not_gt hzN
        have hW : 0 ≤ W z := concreteAnimalWeight_nonneg hp0.le hp1.le z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hscore hW
      _ = ((d : ℝ) * x * n) * ∑ z ∈ N, W z := by rw [Finset.mul_sum]
  have hexceptional : ‖∑ z ∈ E, W z * R z‖ ≤
      (((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * n) * ∑ z ∈ E, W z := by
    calc
      ‖∑ z ∈ E, W z * R z‖ ≤ ∑ z ∈ E, ‖W z * R z‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ E,
          (((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * n) * W z := by
        apply Finset.sum_le_sum
        intro z hz
        have hzA : z ∈ animalParameterPairs d n := by
          exact (Finset.mem_filter.mp hz).1
        have hm := (Finset.mem_Icc.mp (Finset.mem_product.mp hzA).1).2
        have hb := (Finset.mem_Icc.mp (Finset.mem_product.mp hzA).2).2
        have hmR : (z.1 : ℝ) ≤ d * n := by exact_mod_cast hm
        have hbR : (z.2 : ℝ) ≤ 2 * d * n := by exact_mod_cast hb
        have hmp : (z.1 : ℝ) / p ≤ (d : ℝ) * n / p₁ := by
          exact div_le_div₀ (by positivity) hmR hp₁0 hp₁p
        have hbq : (z.2 : ℝ) / (1 - p) ≤ (2 * d : ℝ) * n / (1 - p₂) := by
          exact div_le_div₀ (by positivity) hbR hq₂ (sub_le_sub_left hpp₂ 1)
        have hmpNonneg : 0 ≤ (z.1 : ℝ) / p := div_nonneg (Nat.cast_nonneg _) hp0.le
        have hbqNonneg : 0 ≤ (z.2 : ℝ) / (1 - p) :=
          div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp1.le)
        have hscore : |R z| ≤
            ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * n := by
          unfold R animalDerivativeScore
          calc
            |(z.1 : ℝ) / p - (z.2 : ℝ) / (1 - p)| ≤
                (z.1 : ℝ) / p + (z.2 : ℝ) / (1 - p) :=
              (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hmpNonneg, abs_of_nonneg hbqNonneg])
            _ ≤ (d : ℝ) * n / p₁ + (2 * d : ℝ) * n / (1 - p₂) :=
              add_le_add hmp hbq
            _ = ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * n := by ring
        have hW : 0 ≤ W z := concreteAnimalWeight_nonneg hp0.le hp1.le z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hscore hW
      _ = (((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * n) *
          ∑ z ∈ E, W z := by rw [Finset.mul_sum]
  rw [concreteClusterDensityLevelDerivative_eq_ratio hp0 hp1, hsplit]
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn0)]
  calc
    1 / (n : ℝ) * ‖(∑ z ∈ E, W z * R z) + ∑ z ∈ N, W z * R z‖ ≤
        1 / (n : ℝ) *
          (‖∑ z ∈ E, W z * R z‖ + ‖∑ z ∈ N, W z * R z‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 1 / (n : ℝ) *
        ((((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * n) * ∑ z ∈ E, W z +
          ((d : ℝ) * x * n) * ∑ z ∈ N, W z) := by gcongr
    _ = ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * ∑ z ∈ E, W z +
        (d : ℝ) * x * ∑ z ∈ N, W z := by field_simp
    _ ≤ (d : ℝ) * x * ∑ z ∈ A, W z +
        ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) * ∑ z ∈ E, W z := by
      have hNA : N ⊆ A := Finset.filter_subset _ _
      have hsumNA : ∑ z ∈ N, W z ≤ ∑ z ∈ A, W z :=
        Finset.sum_le_sum_of_subset_of_nonneg hNA (fun z _hzA _hzN ↦
          concreteAnimalWeight_nonneg hp0.le hp1.le z)
      have hdx : 0 ≤ (d : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0.le
      nlinarith [mul_le_mul_of_nonneg_left hsumNA hdx]

/-- Uniform-on-compact level bound used to prove unconditional differentiability in the open
interval.  The second term is a polynomial times one fixed geometric sequence. -/
theorem norm_concreteClusterDensityLevelDerivative_le_geometric
    {d n : ℕ} {p₁ p p₂ x : ℝ} (hd : 0 < d) (hn : 2 ≤ n)
    (hp₁0 : 0 < p₁) (hp₁p : p₁ ≤ p) (hpp₂ : p ≤ p₂) (hp₂1 : p₂ < 1)
    (hx0 : 0 < x) (hx : x ≤ 1 / 100) :
    ‖concreteClusterDensityLevelDerivative d n p‖ ≤
      (d : ℝ) * x * finiteClusterSizeProbability d ⟨p, hp₁0.le.trans hp₁p,
        hpp₂.trans hp₂1.le⟩ n +
      ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) *
        (3 * d ^ 2 * n ^ 2 : ℕ) *
          Real.exp (-((n : ℝ) * x ^ 2 * p₁ ^ 2 * (1 - p₂) / 3)) := by
  have hp0 : 0 < p := hp₁0.trans_le hp₁p
  have hp1 : p < 1 := hpp₂.trans_lt hp₂1
  have hsplit := norm_concreteClusterDensityLevelDerivative_le_split
    hd hn hp₁0 hp₁p hpp₂ hp₂1 hx0
  have htotal :
      ∑ z ∈ animalParameterPairs d n, concreteAnimalWeight d n p z =
        finiteClusterSizeProbability d ⟨p, hp0.le, hp1.le⟩ n := by
    rw [finiteClusterSizeProbability_eq_sum_cubicAnimalCount hd n ⟨p, hp0.le, hp1.le⟩]
    rfl
  have hexceptional :
      ∑ z ∈ exceptionalAnimalPairs d n p x, concreteAnimalWeight d n p z ≤
        (3 * d ^ 2 * n ^ 2 : ℕ) *
          Real.exp (-((n : ℝ) * x ^ 2 * p₁ ^ 2 * (1 - p₂) / 3)) := by
    calc
      ∑ z ∈ exceptionalAnimalPairs d n p x, concreteAnimalWeight d n p z ≤
          (3 * d ^ 2 * n ^ 2 : ℕ) *
            Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3)) := by
        simpa [concreteAnimalWeight] using
          cubicAnimal_largeDeviation_sharp hd hn hp0 hp1 hx0 hx
      _ ≤ (3 * d ^ 2 * n ^ 2 : ℕ) *
          Real.exp (-((n : ℝ) * x ^ 2 * p₁ ^ 2 * (1 - p₂) / 3)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.exp_le_exp.mpr
        have hpSq : p₁ ^ 2 ≤ p ^ 2 := by nlinarith
        have hq : 1 - p₂ ≤ 1 - p := sub_le_sub_left hpp₂ 1
        have hprod : p₁ ^ 2 * (1 - p₂) ≤ p ^ 2 * (1 - p) := by
          exact mul_le_mul hpSq hq (sub_nonneg.mpr hp₂1.le) (sq_nonneg p)
        have hnx : 0 ≤ (n : ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
        nlinarith [mul_le_mul_of_nonneg_left hprod hnx]
  rw [htotal] at hsplit
  calc
    ‖concreteClusterDensityLevelDerivative d n p‖ ≤
        (d : ℝ) * x * finiteClusterSizeProbability d ⟨p, hp0.le, hp1.le⟩ n +
          ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) *
            ∑ z ∈ exceptionalAnimalPairs d n p x, concreteAnimalWeight d n p z := hsplit
    _ ≤ (d : ℝ) * x * finiteClusterSizeProbability d ⟨p, hp0.le, hp1.le⟩ n +
        ((d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)) *
          ((3 * d ^ 2 * n ^ 2 : ℕ) *
            Real.exp (-((n : ℝ) * x ^ 2 * p₁ ^ 2 * (1 - p₂) / 3))) := by
      gcongr
    _ = _ := by ring

def concreteClusterDensityDerivativePartialSum (d N : ℕ) (p : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, concreteClusterDensityLevelDerivative d n p

def concreteClusterDensityPartialSum (d N : ℕ) (p : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, concreteClusterDensityLevel d n p

theorem concreteClusterDensityPartialSum_hasDerivAt (d N : ℕ) (p : ℝ) :
    HasDerivAt (concreteClusterDensityPartialSum d N)
      (concreteClusterDensityDerivativePartialSum d N p) p := by
  exact HasDerivAt.fun_sum fun n _hn ↦ concreteClusterDensityLevel_hasDerivAt d n p

theorem concreteClusterDensityDerivativePartialSum_continuous (d N : ℕ) :
    Continuous (concreteClusterDensityDerivativePartialSum d N) := by
  unfold concreteClusterDensityDerivativePartialSum concreteClusterDensityLevelDerivative
  fun_prop

/-- On every compact interval contained in `(0,1)`, the grouped derivative partial sums are
uniformly Cauchy.  This is the exact analytic conclusion of Grimmett's estimates (4.33)–(4.35),
without a summable-majorant hypothesis. -/
theorem concreteClusterDensityDerivativePartialSum_uniformCauchy
    {d : ℕ} (hd : 0 < d) {p₁ p₂ : ℝ} (hp₁0 : 0 < p₁)
    (hp₂1 : p₂ < 1) :
    UniformCauchySeqOn (concreteClusterDensityDerivativePartialSum d) Filter.atTop
      (Icc p₁ p₂) := by
  refine (Metric.uniformCauchySeqOn_iff
    (F := concreteClusterDensityDerivativePartialSum d) (s := Icc p₁ p₂)).2 ?_
  intro ε hε
  let x : ℝ := min (1 / 100) (ε / (4 * d))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hx0 : 0 < x := lt_min (by norm_num) (div_pos hε (by positivity))
  have hx : x ≤ 1 / 100 := min_le_left _ _
  have hdx : (d : ℝ) * x ≤ ε / 4 := by
    have hx' : x ≤ ε / (4 * d) := min_le_right _ _
    calc
      (d : ℝ) * x ≤ (d : ℝ) * (ε / (4 * d)) :=
        mul_le_mul_of_nonneg_left hx' hdR.le
      _ = ε / 4 := by field_simp
  let C : ℝ := (d : ℝ) / p₁ + (2 * d : ℝ) / (1 - p₂)
  let r : ℝ := x ^ 2 * p₁ ^ 2 * (1 - p₂) / 3
  let U : ℕ → ℝ := fun n ↦
    C * (3 * d ^ 2 * n ^ 2 : ℕ) * Real.exp (-(n : ℝ) * r)
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hU : Summable U := by
    have hbase := (Real.summable_pow_mul_exp_neg_nat_mul 2 hr).mul_left
      (C * (3 * d ^ 2 : ℕ))
    simpa only [U, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc, mul_left_comm,
      mul_comm, neg_mul, mul_neg] using hbase
  have hUcauchy : CauchySeq (fun N : ℕ ↦ ∑ n ∈ Finset.range N, U n) :=
    hU.hasSum.tendsto_sum_nat.cauchySeq
  rw [Metric.cauchySeq_iff] at hUcauchy
  obtain ⟨N₀, hN₀⟩ := hUcauchy (ε / 2) (half_pos hε)
  refine ⟨max 2 N₀, fun m hm n hn p hp ↦ ?_⟩
  have hordered : ∀ a b : ℕ, max 2 N₀ ≤ a → max 2 N₀ ≤ b → a ≤ b →
      dist (concreteClusterDensityDerivativePartialSum d b p)
        (concreteClusterDensityDerivativePartialSum d a p) < ε := by
    intro a b ha hb hab
    have ha2 : 2 ≤ a := le_trans (le_max_left _ _) ha
    have haN : N₀ ≤ a := le_trans (le_max_right _ _) ha
    have hbN : N₀ ≤ b := le_trans (le_max_right _ _) hb
    have hdiff : concreteClusterDensityDerivativePartialSum d b p -
        concreteClusterDensityDerivativePartialSum d a p =
          ∑ k ∈ Finset.Ico a b, concreteClusterDensityLevelDerivative d k p := by
      simp only [concreteClusterDensityDerivativePartialSum]
      rw [← Finset.sum_Ico_eq_sub _ hab]
    have hlevel : ∀ k ∈ Finset.Ico a b,
        ‖concreteClusterDensityLevelDerivative d k p‖ ≤
          (d : ℝ) * x * finiteClusterSizeProbability d
            ⟨p, hp₁0.le.trans hp.1, hp.2.trans hp₂1.le⟩ k + U k := by
      intro k hk
      have hk2 : 2 ≤ k := le_trans ha2 (Finset.mem_Ico.mp hk).1
      convert norm_concreteClusterDensityLevelDerivative_le_geometric hd hk2 hp₁0 hp.1 hp.2
        hp₂1 hx0 hx using 1 <;> dsimp only [U, C, r] <;> ring_nf
    have hprob :
        ∑ k ∈ Finset.Ico a b,
            finiteClusterSizeProbability d ⟨p, hp₁0.le.trans hp.1,
              hp.2.trans hp₂1.le⟩ k ≤ 1 :=
      sum_finiteClusterSizeProbability_le_one d
        ⟨p, hp₁0.le.trans hp.1, hp.2.trans hp₂1.le⟩ (Finset.Ico a b)
    have hU_nonneg : ∀ k, 0 ≤ U k := by
      intro k
      dsimp only [U, C]
      positivity
    have hUsum : ∑ k ∈ Finset.Ico a b, U k < ε / 2 := by
      have hcauchy := hN₀ b hbN a haN
      rw [Real.dist_eq] at hcauchy
      have hpartial : (∑ k ∈ Finset.range b, U k) -
          ∑ k ∈ Finset.range a, U k = ∑ k ∈ Finset.Ico a b, U k := by
        rw [Finset.sum_Ico_eq_sub _ hab]
      rw [hpartial, abs_of_nonneg (Finset.sum_nonneg fun k _hk ↦ hU_nonneg k)] at hcauchy
      exact hcauchy
    rw [Real.dist_eq, hdiff]
    calc
      |∑ k ∈ Finset.Ico a b, concreteClusterDensityLevelDerivative d k p| ≤
          ∑ k ∈ Finset.Ico a b, ‖concreteClusterDensityLevelDerivative d k p‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_sum_le (Finset.Ico a b) fun k ↦ concreteClusterDensityLevelDerivative d k p)
      _ ≤ ∑ k ∈ Finset.Ico a b,
          ((d : ℝ) * x * finiteClusterSizeProbability d
            ⟨p, hp₁0.le.trans hp.1, hp.2.trans hp₂1.le⟩ k + U k) :=
        Finset.sum_le_sum hlevel
      _ = (d : ℝ) * x *
            ∑ k ∈ Finset.Ico a b, finiteClusterSizeProbability d
              ⟨p, hp₁0.le.trans hp.1, hp.2.trans hp₂1.le⟩ k +
            ∑ k ∈ Finset.Ico a b, U k := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (d : ℝ) * x + ∑ k ∈ Finset.Ico a b, U k := by
        have hdx0 : 0 ≤ (d : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0.le
        simpa [add_comm] using
          add_le_add_right (mul_le_of_le_one_right hdx0 hprob)
            (∑ k ∈ Finset.Ico a b, U k)
      _ < ε / 4 + ε / 2 := add_lt_add_of_le_of_lt hdx hUsum
      _ < ε := by linarith
  rcases le_total n m with hnm | hmn
  · exact hordered n m hn hm hnm
  · rw [dist_comm]
    exact hordered m n hm hn hmn

theorem summable_concreteClusterDensityLevelDerivative
    {d : ℕ} (hd : 0 < d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Summable fun n : ℕ ↦ concreteClusterDensityLevelDerivative d n p := by
  let x : ℝ := 1 / 100
  let C : ℝ := (d : ℝ) / p + (2 * d : ℝ) / (1 - p)
  let r : ℝ := x ^ 2 * p ^ 2 * (1 - p) / 3
  let U : ℕ → ℝ := fun n ↦
    C * (3 * d ^ 2 * n ^ 2 : ℕ) * Real.exp (-(n : ℝ) * r)
  have hx0 : 0 < x := by norm_num [x]
  have hx : x ≤ 1 / 100 := le_rfl
  have hr : 0 < r := by
    dsimp only [r]
    positivity
  have hU : Summable U := by
    have hbase := (Real.summable_pow_mul_exp_neg_nat_mul 2 hr).mul_left
      (C * (3 * d ^ 2 : ℕ))
    simpa only [U, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc, mul_left_comm,
      mul_comm, neg_mul, mul_neg] using hbase
  let q : I := ⟨p, hp0.le, hp1.le⟩
  have hP : Summable fun n : ℕ ↦
      (d : ℝ) * x * finiteClusterSizeProbability d q n :=
    (summable_finiteClusterSizeProbability d q).mul_left ((d : ℝ) * x)
  have hmajorant : Summable fun n : ℕ ↦
      (d : ℝ) * x * finiteClusterSizeProbability d q n + U n := hP.add hU
  apply hmajorant.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  convert norm_concreteClusterDensityLevelDerivative_le_geometric hd hn hp0 le_rfl le_rfl
    hp1 hx0 hx using 1 <;> dsimp only [q, U, C, r] <;> ring_nf

theorem summable_concreteClusterDensityLevel
    {d : ℕ} (hd : 0 < d) (p : I) :
    Summable fun n : ℕ ↦ concreteClusterDensityLevel d n p := by
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
  have hcoeff : Summable fun n : ℕ ↦
      (1 / (n : ℝ)) * finiteClusterSizeProbability d p n :=
    (summable_finiteClusterSizeProbability d p).of_nonneg_of_le hcoeffNonneg hcoeffLe
  exact hcoeff.congr fun n ↦ (concreteClusterDensityLevel_eq_probability hd n p).symm

theorem concreteClusterDensityDerivativePartialSum_tendstoUniformlyOn
    {d : ℕ} (hd : 0 < d) {p₁ p₂ : ℝ} (hp₁0 : 0 < p₁) (hp₂1 : p₂ < 1) :
    TendstoUniformlyOn (concreteClusterDensityDerivativePartialSum d)
      (concreteClusterDensityDerivativeSeries d) Filter.atTop (Icc p₁ p₂) := by
  apply (concreteClusterDensityDerivativePartialSum_uniformCauchy hd hp₁0 hp₂1).tendstoUniformlyOn_of_tendsto
  intro p hp
  have hsum := summable_concreteClusterDensityLevelDerivative hd
    (hp₁0.trans_le hp.1) (hp.2.trans_lt hp₂1)
  simpa only [concreteClusterDensityDerivativePartialSum,
    concreteClusterDensityDerivativeSeries] using hsum.hasSum.tendsto_sum_nat

/-- **Grimmett, Theorem 4.31, unconditional interior form.**

The concrete open-cluster-density animal series is differentiable at every `p ∈ (0,1)`, including
the critical probability, and its derivative is exactly the grouped version of equation (4.32).
No coefficient table, uniform majorant, or differentiability assumption remains as a parameter. -/
theorem concreteClusterDensitySeries_hasDerivAt
    {d : ℕ} (hd : 0 < d) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (concreteClusterDensitySeries d)
      (concreteClusterDensityDerivativeSeries d p) p := by
  let p₁ := p / 2
  let p₂ := (1 + p) / 2
  have hp₁0 : 0 < p₁ := by dsimp only [p₁]; linarith
  have hp₂1 : p₂ < 1 := by dsimp only [p₂]; linarith
  have hp_mem : p ∈ Ioo p₁ p₂ := by
    dsimp only [p₁, p₂]
    constructor <;> linarith
  have hderiv := concreteClusterDensityDerivativePartialSum_tendstoUniformlyOn
    hd hp₁0 hp₂1
  have hderivOpen : TendstoUniformlyOn
      (concreteClusterDensityDerivativePartialSum d)
      (concreteClusterDensityDerivativeSeries d) Filter.atTop (Ioo p₁ p₂) :=
    hderiv.mono (Ioo_subset_Icc_self)
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hderivOpen
  · filter_upwards with N y _hy
    exact concreteClusterDensityPartialSum_hasDerivAt d N y
  · intro y hy
    let q : I := ⟨y, (hp₁0.trans hy.1).le, (hy.2.trans hp₂1).le⟩
    have hsum := summable_concreteClusterDensityLevel hd q
    simpa only [concreteClusterDensityPartialSum, concreteClusterDensitySeries] using
      hsum.hasSum.tendsto_sum_nat
  · exact hp_mem

theorem concreteClusterDensityDerivativeSeries_continuousOn_Ioo
    {d : ℕ} (hd : 0 < d) :
    ContinuousOn (concreteClusterDensityDerivativeSeries d) (Ioo 0 1) := by
  intro p hp
  let p₁ := p / 2
  let p₂ := (1 + p) / 2
  have hp₁0 : 0 < p₁ := by dsimp only [p₁]; linarith [hp.1]
  have hp₂1 : p₂ < 1 := by dsimp only [p₂]; linarith [hp.2]
  have hp₁p : p₁ < p := by dsimp only [p₁]; linarith [hp.1]
  have hpp₂ : p < p₂ := by dsimp only [p₂]; linarith [hp.2]
  have huniform := concreteClusterDensityDerivativePartialSum_tendstoUniformlyOn
    hd hp₁0 hp₂1
  have hcontinuous : ContinuousOn (concreteClusterDensityDerivativeSeries d) (Icc p₁ p₂) :=
    huniform.continuousOn ((Filter.Eventually.of_forall fun N ↦
      (concreteClusterDensityDerivativePartialSum_continuous d N).continuousOn).frequently)
  exact (hcontinuous.continuousAt (Icc_mem_nhds hp₁p hpp₂)).continuousWithinAt

/-- The unconditional `C¹` conclusion of Theorem 4.31 on the open unit interval. -/
theorem concreteClusterDensitySeries_contDiffOn_Ioo
    {d : ℕ} (hd : 0 < d) :
    ContDiffOn ℝ 1 (concreteClusterDensitySeries d) (Ioo 0 1) := by
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioo (0 : ℝ) 1)).2
  constructor
  · intro p hp
    exact (concreteClusterDensitySeries_hasDerivAt hd hp.1 hp.2).differentiableAt.differentiableWithinAt
  · exact (concreteClusterDensityDerivativeSeries_continuousOn_Ioo hd).congr fun p hp ↦
      (concreteClusterDensitySeries_hasDerivAt hd hp.1 hp.2).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Ioo (0 : ℝ) 1) p hp)

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

theorem concreteClusterDensitySeries_eq_openClustersPerVertex
    {d : ℕ} (hd : 0 < d) (p : I) :
    concreteClusterDensitySeries d p = openClustersPerVertex d p := by
  rw [concreteClusterDensitySeries,
    openClustersPerVertex_eq_tsum_finiteClusterSizeProbability]
  exact tsum_congr fun n ↦ concreteClusterDensityLevel_eq_probability hd n p

/-- **Grimmett, Theorem 4.20, including the `n = 1` endpoint.**

This is the source-facing concrete theorem: for every positive animal size and the explicit
uniform range `0 < x ≤ 1/100`, the exceptional animal mass has Grimmett's prefactor and exponent.
The `n ≥ 2` case is `cubicAnimal_largeDeviation_sharp`; for `n = 1`, the entire exceptional sum
is bounded by the cluster-size probability, while the displayed right-hand side is at least one. -/
theorem cubicAnimal_largeDeviation_sharp_one_le {d n : ℕ} {p x : ℝ}
    (hd : 0 < d) (hn : 1 ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hx0 : 0 < x) (hx : x ≤ 1 / 100) :
    ∑ z ∈ exceptionalAnimalPairs d n p x,
        (cubicAnimalCount d n z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
      (3 * d ^ 2 * n ^ 2 : ℕ) *
        Real.exp (-((n : ℝ) * x ^ 2 * p ^ 2 * (1 - p) / 3)) := by
  by_cases hn2 : 2 ≤ n
  · exact cubicAnimal_largeDeviation_sharp hd hn2 hp0 hp1 hx0 hx
  · have hnEq : n = 1 := by omega
    subst n
    simp only [one_pow, mul_one, Nat.cast_one, one_mul] at ⊢
    let pI : I := ⟨p, hp0.le, hp1.le⟩
    have hsubset : exceptionalAnimalPairs d 1 p x ⊆ animalParameterPairs d 1 := by
      exact Finset.filter_subset _ _
    have hsumLe :
        ∑ z ∈ exceptionalAnimalPairs d 1 p x,
            (cubicAnimalCount d 1 z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
          ∑ z ∈ animalParameterPairs d 1,
            (cubicAnimalCount d 1 z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z _hz _hzExc
      positivity
    have hx1 : x ≤ 1 := hx.trans (by norm_num)
    have hxSq : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - x)]
    have hpSq : p ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - p)]
    have hq0 : 0 ≤ 1 - p := by linarith
    have hq1 : 1 - p ≤ 1 := by linarith
    have hxp : x ^ 2 * p ^ 2 ≤ 1 := by
      calc
        x ^ 2 * p ^ 2 ≤ 1 * p ^ 2 := mul_le_mul_of_nonneg_right hxSq (sq_nonneg p)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpSq zero_le_one
        _ = 1 := one_mul 1
    have hall : x ^ 2 * p ^ 2 * (1 - p) ≤ 1 := by
      calc
        x ^ 2 * p ^ 2 * (1 - p) ≤ 1 * (1 - p) :=
          mul_le_mul_of_nonneg_right hxp hq0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hq1 zero_le_one
        _ = 1 := one_mul 1
    let a : ℝ := x ^ 2 * p ^ 2 * (1 - p) / 3
    have ha : a ≤ 1 / 3 := by
      dsimp only [a]
      exact div_le_div_of_nonneg_right hall (by norm_num)
    have hExp : (2 / 3 : ℝ) ≤ Real.exp (-a) := by
      calc
        (2 / 3 : ℝ) ≤ 1 - a := by linarith
        _ = 1 + (-a) := by ring
        _ ≤ Real.exp (-a) := by simpa [add_comm] using Real.add_one_le_exp (-a)
    have hd1 : 1 ≤ d := by omega
    have hdSq : 1 ≤ d ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hd1 hd1
    have hcoefNat : 3 ≤ 3 * d ^ 2 := by omega
    have hcoef : (3 : ℝ) ≤ (3 * d ^ 2 : ℕ) := by exact_mod_cast hcoefNat
    have hRhs : (1 : ℝ) ≤ (3 * d ^ 2 : ℕ) * Real.exp (-a) := by
      calc
        (1 : ℝ) ≤ 3 * (2 / 3 : ℝ) := by norm_num
        _ ≤ (3 * d ^ 2 : ℕ) * Real.exp (-a) :=
          mul_le_mul hcoef hExp (by norm_num) (by positivity)
    calc
      ∑ z ∈ exceptionalAnimalPairs d 1 p x,
          (cubicAnimalCount d 1 z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 ≤
          ∑ z ∈ animalParameterPairs d 1,
            (cubicAnimalCount d 1 z.1 z.2 : ℝ) * p ^ z.1 * (1 - p) ^ z.2 := hsumLe
      _ = finiteClusterSizeProbability d pI 1 := by
        symm
        exact finiteClusterSizeProbability_eq_sum_cubicAnimalCount hd 1 pI
      _ ≤ 1 := finiteClusterSizeProbability_le_one d pI 1
      _ ≤ (3 * d ^ 2 : ℕ) * Real.exp (-(x ^ 2 * p ^ 2 * (1 - p) / 3)) := by
        simpa [a] using hRhs

#print axioms cubicAnimal_largeDeviation_sharp_one_le

end

end Percolation
