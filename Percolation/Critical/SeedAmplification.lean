import Percolation.Critical.BoundaryOrthants

/-!
# Seed amplification geometry for Grimmett Lemma 7.9

The book partitions a face quadrant into squares and temporarily assumes `2m+1 ∣ n+1`.
We instead assign every contact a canonical clamped seed center.  The associated seed box lies
inside the layered region `T(m,n)` for every `n ≥ 2m`, so the eventual contact estimate may be
used without an arithmetic side condition.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Clamp a nonnegative boundary coordinate into the interval `[m,n-m]`. -/
def clampBoundaryCoordinate (m n : ℕ) (z : ℤ) : ℤ :=
  if z < (m : ℤ) then m else if (n - m : ℕ) < z then n - m else z

/-- Canonical center of a seed adjacent to the positive `i`-face at a boundary point `y`. -/
def canonicalBoundarySeedCenter {d : ℕ}
    (i : Fin d) (m n : ℕ) (y : Cubic d) : Cubic d :=
  fun j => if j = i then (n + m + 1 : ℕ) else clampBoundaryCoordinate m n (y j)

theorem clampBoundaryCoordinate_mem_interval
    {m n : ℕ} (hmn : 2 * m ≤ n) {z : ℤ} (_hz0 : 0 ≤ z) (_hzn : z ≤ n) :
    (m : ℤ) ≤ clampBoundaryCoordinate m n z ∧
      clampBoundaryCoordinate m n z ≤ (n - m : ℕ) := by
  unfold clampBoundaryCoordinate
  split_ifs with hlow hhigh
  · constructor <;> norm_num
    omega
  · constructor <;> omega
  · constructor <;> omega

theorem abs_sub_clampBoundaryCoordinate_le
    {m n : ℕ} (hmn : 2 * m ≤ n) {z : ℤ} (hz0 : 0 ≤ z) (hzn : z ≤ n) :
    |z - clampBoundaryCoordinate m n z| ≤ (m : ℤ) := by
  unfold clampBoundaryCoordinate
  split_ifs with hlow hhigh
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega
  · simp

theorem cubicStepFrom_mem_canonicalBoundarySeedBox
    {d m n : ℕ} (i : Fin d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n) :
    cubicStepFrom y (i, true) ∈
      cubicMetricBox d (canonicalBoundarySeedCenter i m n y) m := by
  rw [mem_cubicMetricBox]
  intro j
  by_cases hji : j = i
  · subst j
    have hyFace := (mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hy).1).1
    simp [canonicalBoundarySeedCenter, cubicStepFrom, cubicDirectionIncrement,
      cubicOrigin] at hyFace ⊢
    omega
  · have hyBounds := (mem_cubicBoxFace.mp
      (mem_seededBoundaryQuadrant_iff.mp hy).1).2 j hji
    have hy0 := (mem_seededBoundaryQuadrant_iff.mp hy).2 j hji
    simp [canonicalBoundarySeedCenter, cubicStepFrom, cubicDirectionIncrement, hji]
    have habs := abs_sub_clampBoundaryCoordinate_le hmn hy0 (by
      simpa [cubicOrigin] using hyBounds.2)
    rw [abs_le] at habs
    constructor <;> omega

theorem canonicalBoundarySeedBoxWithinBoundaryLayer
    {d m n : ℕ} (i : Fin d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n) :
    SeedBoxWithinBoundaryLayer d i m n (canonicalBoundarySeedCenter i m n y) := by
  intro z hz
  have hzBounds := mem_cubicMetricBox.mp hz
  have hyFace := mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hy).1
  let r : ℕ := (z i - (n : ℤ)).toNat
  let base : Cubic d := Function.update z i n
  have hziLower : (n : ℤ) + 1 ≤ z i := by
    have hi := hzBounds i
    simp [canonicalBoundarySeedCenter] at hi
    omega
  have hziUpper : z i ≤ (n : ℤ) + (2 * m + 1 : ℕ) := by
    have hi := hzBounds i
    simp [canonicalBoundarySeedCenter] at hi
    omega
  have hrCast : (r : ℤ) = z i - n := by
    dsimp [r]
    rw [Int.toNat_of_nonneg]
    omega
  have hr1 : 1 ≤ r := by
    omega
  have hr2 : r ≤ 2 * m + 1 := by
    omega
  have hbaseFace : base ∈ cubicBoxFace d cubicOrigin n i true := by
    rw [mem_cubicBoxFace]
    constructor
    · simp [base, cubicOrigin]
    · intro j hji
      have hj := hzBounds j
      have hy0 : 0 ≤ y j := (mem_seededBoundaryQuadrant_iff.mp hy).2 j hji
      have hyn : y j ≤ (n : ℤ) := by
        simpa [cubicOrigin] using (hyFace.2 j hji).2
      have hc := clampBoundaryCoordinate_mem_interval hmn hy0 hyn
      simp [base, canonicalBoundarySeedCenter, hji, cubicOrigin] at hj ⊢
      constructor <;> omega
  have hbaseQuadrant : base ∈ seededBoundaryQuadrant d i n := by
    rw [mem_seededBoundaryQuadrant_iff]
    refine ⟨hbaseFace, ?_⟩
    intro j hji
    have hj := hzBounds j
    have hy0 : 0 ≤ y j := (mem_seededBoundaryQuadrant_iff.mp hy).2 j hji
    have hyn : y j ≤ (n : ℤ) := by
      simpa [cubicOrigin] using (hyFace.2 j hji).2
    have hc := clampBoundaryCoordinate_mem_interval hmn hy0 hyn
    have hbasej : base j = z j := by simp [base, hji]
    rw [hbasej]
    simp [canonicalBoundarySeedCenter, hji] at hj
    omega
  refine ⟨r, hr1, hr2, base, hbaseQuadrant, ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    rw [cubicTranslateAlongCoordinate_same]
    have hbasei : base i = (n : ℤ) := by simp [base]
    rw [hbasei]
    omega
  · simp [base, cubicTranslateAlongCoordinate_of_ne, hji]

/-- Opening the outward edge and the canonical seed box makes a contacted boundary point a
member of Grimmett's random target set `K(m,n)`. -/
theorem isSeededBoundaryPoint_of_canonicalSeed
    {d m n : ℕ} (i : Fin d) {y : Cubic d} {omega : EdgeConfiguration d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n)
    (hedge : cubicStepEdge y (i, true) ∈ omega)
    (hseed : omega ∈ cubicSeedEvent d (canonicalBoundarySeedCenter i m n y) m) :
    IsSeededBoundaryPoint d i m n omega y :=
  ⟨hy, hedge, canonicalBoundarySeedCenter i m n y,
    cubicStepFrom_mem_canonicalBoundarySeedBox i hmn hy,
    canonicalBoundarySeedBoxWithinBoundaryLayer i hmn hy, hseed⟩

end Percolation
