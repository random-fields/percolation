import Percolation.Critical.DynamicRevealBudget
import Percolation.Critical.RegionTranslation

/-!
# Steering geometry for the Grimmett--Marstrand block construction

The first nontrivial steering move on pp. 158--160 starts from a canonical seed beyond the
positive face of `B(n)` and uses the opposite transverse quadrant `T*(m,n)`.  The lemmas below
formalize the literal coordinate calculation: the exploratory copy of `B(n)` stays in the
radius-`2N` origin box, while the steered boundary layer stays in the half-way bond box centered
at `2N eᵢ`, where `N = m+n+1`.
-/

namespace Percolation

/-- The steered quadrant `T*(n)`: positive `i`-face and nonpositive transverse coordinates. -/
noncomputable def steeredPositiveBoundaryQuadrant
    (d : ℕ) (i : Fin d) (n : ℕ) : Finset (Cubic d) :=
  (cubicBoxFace d cubicOrigin n i true).filter fun x ↦
    ∀ j : Fin d, j ≠ i → x j ≤ 0

@[simp]
theorem mem_steeredPositiveBoundaryQuadrant_iff
    {d n : ℕ} {i : Fin d} {x : Cubic d} :
    x ∈ steeredPositiveBoundaryQuadrant d i n ↔
      x ∈ cubicBoxFace d cubicOrigin n i true ∧ ∀ j, j ≠ i → x j ≤ 0 := by
  classical
  simp [steeredPositiveBoundaryQuadrant]

/-- The layered steered region `T*(m,n)` from the proof of Theorem 7.2. -/
def steeredPositiveBoundaryLayerRegion
    (d : ℕ) (i : Fin d) (m n : ℕ) : Set (Cubic d) :=
  {z | ∃ r : ℕ, 1 ≤ r ∧ r ≤ 2 * m + 1 ∧
    ∃ y ∈ steeredPositiveBoundaryQuadrant d i n,
      z = cubicTranslateAlongCoordinate y i r}

/-- The local restart region: an exploratory box together with its steered target layer. -/
def steeredPositiveRestartRegion
    (d : ℕ) (i : Fin d) (m n : ℕ) : Set (Cubic d) :=
  (cubicMetricBox d cubicOrigin n : Set (Cubic d)) ∪
    steeredPositiveBoundaryLayerRegion d i m n

theorem canonicalBoundarySeedCenter_same
    {d m n : ℕ} (i : Fin d) (y : Cubic d) :
    canonicalBoundarySeedCenter i m n y i = (m + n + 1 : ℕ) := by
  simp [canonicalBoundarySeedCenter]
  omega

theorem canonicalBoundarySeedCenter_transverse_bounds
    {d m n : ℕ} (i : Fin d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n)
    {j : Fin d} (hji : j ≠ i) :
    (m : ℤ) ≤ canonicalBoundarySeedCenter i m n y j ∧
      canonicalBoundarySeedCenter i m n y j ≤ (n - m : ℕ) := by
  have hyFace := mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hy).1
  have hy0 := (mem_seededBoundaryQuadrant_iff.mp hy).2 j hji
  have hyn : y j ≤ (n : ℤ) := by
    simpa [cubicOrigin] using (hyFace.2 j hji).2
  simpa [canonicalBoundarySeedCenter, hji] using
    clampBoundaryCoordinate_mem_interval hmn hy0 hyn

/-- The exploratory `B(n)` around the first boundary seed remains in the radius-`2N` box at
the old site. -/
theorem translated_seedExplorationBox_subset_oldEndpointBox
    {d m n : ℕ} (i : Fin d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n) :
    cubicTranslateRegion cubicOrigin (canonicalBoundarySeedCenter i m n y)
        (cubicMetricBox d cubicOrigin n) ⊆
      (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  change cubicTranslate cubicOrigin (canonicalBoundarySeedCenter i m n y) w ∈
    cubicMetricBox d cubicOrigin (2 * (m + n + 1))
  rw [mem_cubicMetricBox]
  intro j
  have hwj := mem_cubicMetricBox.mp hw j
  by_cases hji : j = i
  · subst j
    simp [cubicTranslate, cubicOrigin, canonicalBoundarySeedCenter_same] at hwj ⊢
    omega
  · have hc := canonicalBoundarySeedCenter_transverse_bounds i hmn hy hji
    simp [cubicTranslate, cubicOrigin] at hwj ⊢
    constructor <;> omega

/-- The translated `T*(m,n)` lies in the half-way bond box `2N eᵢ+B(N)`.  This is the
coordinate steering assertion omitted after Figure 7.5. -/
theorem translated_steeredBoundaryLayer_subset_halfwayBox
    {d m n : ℕ} (i : Fin d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n) :
    cubicTranslateRegion cubicOrigin (canonicalBoundarySeedCenter i m n y)
        (steeredPositiveBoundaryLayerRegion d i m n) ⊆
      (grimmettMarstrandHalfwayBox d (m + n + 1) cubicOrigin (i, true) :
        Set (Cubic d)) := by
  intro z hz
  rcases hz with ⟨w, ⟨r, hr1, hr2, q, hq, rfl⟩, rfl⟩
  change cubicTranslate cubicOrigin (canonicalBoundarySeedCenter i m n y)
      (cubicTranslateAlongCoordinate q i r) ∈
    cubicMetricBox d
      (grimmettMarstrandBondCenter (m + n + 1) cubicOrigin
        (cubicStepFrom cubicOrigin (i, true)))
      (m + n + 1)
  rw [mem_cubicMetricBox]
  intro j
  have hqFace := mem_cubicBoxFace.mp
    (mem_steeredPositiveBoundaryQuadrant_iff.mp hq).1
  by_cases hji : j = i
  · subst j
    have hqi := hqFace.1
    simp [grimmettMarstrandBondCenter, cubicTranslate, cubicOrigin,
      canonicalBoundarySeedCenter_same, cubicTranslateAlongCoordinate,
      cubicStepFrom, cubicDirectionIncrement] at hqi ⊢
    omega
  · have hc := canonicalBoundarySeedCenter_transverse_bounds i hmn hy hji
    have hqBounds := hqFace.2 j hji
    have hqNonpos := (mem_steeredPositiveBoundaryQuadrant_iff.mp hq).2 j hji
    have hwj : cubicTranslateAlongCoordinate q i r j = q j :=
      cubicTranslateAlongCoordinate_of_ne q hji r
    simp [grimmettMarstrandBondCenter, cubicTranslate, cubicOrigin,
      cubicStepFrom, cubicDirectionIncrement, hji, hwj] at hqBounds ⊢
    constructor <;> omega

/-- Both pieces of the steered restart remain in the two endpoint radius-`2N` boxes. -/
theorem translated_steeredRestartRegion_subset_endpointBoxes
    {d m n : ℕ} (i : Fin d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n) :
    cubicTranslateRegion cubicOrigin (canonicalBoundarySeedCenter i m n y)
        (steeredPositiveRestartRegion d i m n) ⊆
      (cubicMetricBox d cubicOrigin (2 * (m + n + 1)) : Set (Cubic d)) ∪
        (cubicMetricBox d
          (grimmettMarstrandSiteCenter (m + n + 1) (cubicStepFrom cubicOrigin (i, true)))
          (2 * (m + n + 1)) : Set (Cubic d)) := by
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  rcases hw with hw | hw
  · left
    exact translated_seedExplorationBox_subset_oldEndpointBox i hmn hy ⟨w, hw, rfl⟩
  · have hhalf := translated_steeredBoundaryLayer_subset_halfwayBox i hmn hy
      ⟨w, hw, rfl⟩
    exact grimmettMarstrandHalfwayBox_subset_endpointBoxes cubicOrigin (i, true) hhalf

end Percolation
