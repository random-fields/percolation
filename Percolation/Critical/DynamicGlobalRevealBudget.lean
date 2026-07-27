import Percolation.Critical.DynamicBlockGeometry
import Percolation.Critical.DynamicSourceSchedule

/-!
# Global spatial accounting for dynamic-block reveals

The success probability of one non-root Grimmett--Marstrand block uses up to `4d` restart
applications, whereas equation (7.34) counts how many translated radius-`n` reveal boxes can
contain one physical edge.  These are different quantities.  This file begins the global
accounting with a scale-uniform packing lemma for the coarse centers `4Nx`.
-/

namespace Percolation

/-- Coarse sites whose deterministic centers lie within radius `2N` of a physical vertex. -/
def grimmettMarstrandCentersNear {d : ℕ} (N : ℕ) (z : Cubic d) : Set (Cubic d) :=
  {x | grimmettMarstrandSiteCenter N x ∈ cubicMetricBox d z (2 * N)}

/-- The side of `z` on which a coarse center lies, coordinate by coordinate. -/
def grimmettMarstrandCenterSideCode {d : ℕ} (N : ℕ) (z x : Cubic d) : Fin d → Bool :=
  fun i ↦ decide (grimmettMarstrandSiteCenter N x i ≤ z i)

/-- Two coarse centers within radius `2N` of the same vertex and on the same coordinatewise
side of that vertex coincide.  Thus the nearby coarse centers inject into the `2^d` sign
vectors, uniformly in the scale `N`. -/
theorem grimmettMarstrandCenterSideCode_injOn
    {d N : ℕ} (hN : 0 < N) (z : Cubic d) :
    Set.InjOn (grimmettMarstrandCenterSideCode N z)
      (grimmettMarstrandCentersNear N z) := by
  intro x hx y hy hcode
  funext i
  have hxBounds :
      z i - (2 * N : ℕ) ≤ 4 * (N : ℤ) * x i ∧
        4 * (N : ℤ) * x i ≤ z i + (2 * N : ℕ) := by
    simpa [grimmettMarstrandCentersNear, grimmettMarstrandSiteCenter, cubicScale] using
      mem_cubicMetricBox.mp hx i
  have hyBounds :
      z i - (2 * N : ℕ) ≤ 4 * (N : ℤ) * y i ∧
        4 * (N : ℤ) * y i ≤ z i + (2 * N : ℕ) := by
    simpa [grimmettMarstrandCentersNear, grimmettMarstrandSiteCenter, cubicScale] using
      mem_cubicMetricBox.mp hy i
  have hscale : (0 : ℤ) < 4 * (N : ℤ) := by positivity
  have hcodei := congrFun hcode i
  by_cases hxSide : grimmettMarstrandSiteCenter N x i ≤ z i
  · by_cases hySide : grimmettMarstrandSiteCenter N y i ≤ z i
    · have hxSide' : 4 * (N : ℤ) * x i ≤ z i := by
        simpa [grimmettMarstrandSiteCenter, cubicScale] using hxSide
      have hySide' : 4 * (N : ℤ) * y i ≤ z i := by
        simpa [grimmettMarstrandSiteCenter, cubicScale] using hySide
      by_contra hxy
      rcases lt_or_gt_of_ne hxy with hxy | hyx
      · have hstep : x i + 1 ≤ y i := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hstep hscale.le
        have hgap : 4 * (N : ℤ) * x i + 4 * N ≤ 4 * N * y i := calc
          4 * (N : ℤ) * x i + 4 * N = 4 * N * (x i + 1) := by ring
          _ ≤ 4 * N * y i := hmul
        omega
      · have hstep : y i + 1 ≤ x i := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hstep hscale.le
        have hgap : 4 * (N : ℤ) * y i + 4 * N ≤ 4 * N * x i := calc
          4 * (N : ℤ) * y i + 4 * N = 4 * N * (y i + 1) := by ring
          _ ≤ 4 * N * x i := hmul
        omega
    · simp [grimmettMarstrandCenterSideCode, hxSide, hySide] at hcodei
  · by_cases hySide : grimmettMarstrandSiteCenter N y i ≤ z i
    · simp [grimmettMarstrandCenterSideCode, hxSide, hySide] at hcodei
    · have hxSide' : z i < 4 * (N : ℤ) * x i := by
        simpa [grimmettMarstrandSiteCenter, cubicScale] using lt_of_not_ge hxSide
      have hySide' : z i < 4 * (N : ℤ) * y i := by
        simpa [grimmettMarstrandSiteCenter, cubicScale] using lt_of_not_ge hySide
      by_contra hxy
      rcases lt_or_gt_of_ne hxy with hxy | hyx
      · have hstep : x i + 1 ≤ y i := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hstep hscale.le
        have hgap : 4 * (N : ℤ) * x i + 4 * N ≤ 4 * N * y i := calc
          4 * (N : ℤ) * x i + 4 * N = 4 * N * (x i + 1) := by ring
          _ ≤ 4 * N * y i := hmul
        omega
      · have hstep : y i + 1 ≤ x i := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hstep hscale.le
        have hgap : 4 * (N : ℤ) * y i + 4 * N ≤ 4 * N * x i := calc
          4 * (N : ℤ) * y i + 4 * N = 4 * N * (y i + 1) := by ring
          _ ≤ 4 * N * x i := hmul
        omega

/-- Only finitely many coarse centers can lie within radius `2N` of a fixed physical vertex. -/
theorem finite_grimmettMarstrandCentersNear
    {d N : ℕ} (hN : 0 < N) (z : Cubic d) :
    (grimmettMarstrandCentersNear N z).Finite := by
  apply Set.Finite.of_finite_image
  · exact (Set.finite_univ : (Set.univ : Set (Fin d → Bool)).Finite).subset
      (Set.subset_univ _)
  · exact grimmettMarstrandCenterSideCode_injOn hN z

/-- Uniform packing bound for nearby coarse centers. -/
theorem ncard_grimmettMarstrandCentersNear_le
    {d N : ℕ} (hN : 0 < N) (z : Cubic d) :
    (grimmettMarstrandCentersNear N z).ncard ≤ 2 ^ d := by
  have hinj := grimmettMarstrandCenterSideCode_injOn hN z
  have hcard := Set.ncard_le_ncard_of_injOn
    (grimmettMarstrandCenterSideCode N z)
    (s := grimmettMarstrandCentersNear N z)
    (t := Set.univ) (fun _ _ ↦ Set.mem_univ _) hinj Set.finite_univ
  simpa using hcard

/-- A coarse vertex together with its `2d` signed nearest neighbours. -/
noncomputable def cubicClosedNeighborFinset {d : ℕ} (x : Cubic d) : Finset (Cubic d) :=
  insert x ((Finset.univ : Finset (CubicDirection d)).image fun a ↦ cubicStepFrom x a)

@[simp]
theorem mem_cubicClosedNeighborFinset_iff
    {d : ℕ} {x y : Cubic d} :
    y ∈ cubicClosedNeighborFinset x ↔
      y = x ∨ ∃ a : CubicDirection d, cubicStepFrom x a = y := by
  classical
  simp [cubicClosedNeighborFinset]

/-- The closed cubic neighbourhood has at most `2d+1` vertices. -/
theorem card_cubicClosedNeighborFinset_le
    {d : ℕ} (x : Cubic d) :
    (cubicClosedNeighborFinset x).card ≤ 2 * d + 1 := by
  classical
  calc
    (cubicClosedNeighborFinset x).card ≤
        ((Finset.univ : Finset (CubicDirection d)).image
          (fun a ↦ cubicStepFrom x a)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (CubicDirection d)).card + 1 := by
      gcongr
      exact Finset.card_image_le
    _ = 2 * d + 1 := by simp [CubicDirection, Fintype.card_prod, Nat.mul_comm]

/-- Closed cubic neighbourhoods are symmetric. -/
theorem mem_cubicClosedNeighborFinset_comm
    {d : ℕ} {x y : Cubic d}
    (hxy : y ∈ cubicClosedNeighborFinset x) :
    x ∈ cubicClosedNeighborFinset y := by
  rw [mem_cubicClosedNeighborFinset_iff] at hxy ⊢
  rcases hxy with rfl | ⟨a, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨reverseCubicDirection a, cubicStepFrom_reverse x a⟩

/-- The local physical region that can be read while processing the coarse query `v`: the
radius-`2N` boxes around `v` and each of its signed neighbours. -/
def grimmettMarstrandQueryInfluenceRegion
    {d : ℕ} (N : ℕ) (v : Cubic d) : Set (Cubic d) :=
  ⋃ y ∈ (cubicClosedNeighborFinset v : Set (Cubic d)),
    (cubicMetricBox d (grimmettMarstrandSiteCenter N y) (2 * N) : Set (Cubic d))

theorem centeredBox_subset_grimmettMarstrandQueryInfluenceRegion
    {d N : ℕ} {v y : Cubic d}
    (hy : y ∈ cubicClosedNeighborFinset v) :
    (cubicMetricBox d (grimmettMarstrandSiteCenter N y) (2 * N) : Set (Cubic d)) ⊆
      grimmettMarstrandQueryInfluenceRegion N v := by
  intro z hz
  exact Set.mem_iUnion₂.mpr ⟨y, hy, hz⟩

/-- Coarse query sites which can use a bond incident to a coarse center lying within radius
`2N` of `z`.  The reversal symmetry of cubic steps makes this the correct closed-neighbour
enlargement whether the nearby center is the query site or an advertised neighbour. -/
def grimmettMarstrandInfluenceSites {d : ℕ} (N : ℕ) (z : Cubic d) : Set (Cubic d) :=
  ⋃ x ∈ grimmettMarstrandCentersNear N z, (cubicClosedNeighborFinset x : Set (Cubic d))

/-- If a physical vertex lies in the local influence region of a coarse query, that query is
one of the uniformly many influence sites associated with the vertex. -/
theorem mem_grimmettMarstrandInfluenceSites_of_mem_queryInfluenceRegion
    {d N : ℕ} {v z : Cubic d}
    (hz : z ∈ grimmettMarstrandQueryInfluenceRegion N v) :
    v ∈ grimmettMarstrandInfluenceSites N z := by
  rw [grimmettMarstrandQueryInfluenceRegion, Set.mem_iUnion₂] at hz
  obtain ⟨y, hyv, hzy⟩ := hz
  rw [grimmettMarstrandInfluenceSites, Set.mem_iUnion₂]
  refine ⟨y, ?_, mem_cubicClosedNeighborFinset_comm hyv⟩
  rw [grimmettMarstrandCentersNear]
  exact mem_cubicMetricBox_iff_lInfDist_le.mpr <| by
    rw [cubicLInfDist_comm]
    exact mem_cubicMetricBox_iff_lInfDist_le.mp hzy

/-- The scale-uniform coarse influence set is finite. -/
theorem finite_grimmettMarstrandInfluenceSites
    {d N : ℕ} (hN : 0 < N) (z : Cubic d) :
    (grimmettMarstrandInfluenceSites N z).Finite := by
  apply (finite_grimmettMarstrandCentersNear hN z).biUnion
  intro x _hx
  exact (cubicClosedNeighborFinset x).finite_toSet

/-- A safe uniform cardinality bound for the coarse sites whose local two-endpoint boxes can
contain a fixed physical vertex.  The sharper source geometry ultimately reduces the reveal
multiplicity to `2d+1`; this product bound is the scale-independent packing bound available
before that sharpening. -/
theorem ncard_grimmettMarstrandInfluenceSites_le
    {d N : ℕ} (hN : 0 < N) (z : Cubic d) :
    (grimmettMarstrandInfluenceSites N z).ncard ≤ (2 ^ d) * (2 * d + 1) := by
  let near := grimmettMarstrandCentersNear N z
  have hnear : near.Finite := finite_grimmettMarstrandCentersNear hN z
  calc
    (grimmettMarstrandInfluenceSites N z).ncard ≤
        ∑ᶠ x ∈ near, ((cubicClosedNeighborFinset x : Finset (Cubic d)) :
          Set (Cubic d)).ncard := by
      simpa [grimmettMarstrandInfluenceSites, near] using
        hnear.ncard_biUnion_le
          (fun x ↦ ((cubicClosedNeighborFinset x : Finset (Cubic d)) : Set (Cubic d)))
    _ ≤ ∑ᶠ _x ∈ near, (2 * d + 1) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hnear,
        finsum_mem_eq_finite_toFinset_sum _ hnear]
      apply Finset.sum_le_sum
      intro x _hx
      simpa using card_cubicClosedNeighborFinset_le x
    _ = near.ncard * (2 * d + 1) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hnear]
      simp [Set.ncard_eq_toFinset_card near hnear]
    _ ≤ (2 ^ d) * (2 * d + 1) := by
      gcongr
      exact ncard_grimmettMarstrandCentersNear_le hN z

end Percolation
