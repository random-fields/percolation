import Percolation.Critical.RestartGeometry

/-!
# Grimmett--Marstrand dynamic block geometry

This file gives literal finite boxes for the construction on pp. 155--162.  Probability and
adaptive reveal data are added in later files; keeping the geometry independent makes the final
containment in `4 N F + B(2 N)` directly reviewable.
-/

namespace Percolation

open scoped unitInterval

/-- The two radii selected by Lemma 7.17, with the strict separation used in the source. -/
structure GrimmettMarstrandBlock (d : ℕ) where
  m : ℕ
  n : ℕ
  two_mul_m_lt_n : 2 * m < n

namespace GrimmettMarstrandBlock

/-- Grimmett's block half-width `N=m+n+1`. -/
def scale (B : GrimmettMarstrandBlock d) : ℕ :=
  B.m + B.n + 1

theorem m_lt_scale (B : GrimmettMarstrandBlock d) : B.m < B.scale := by
  simp [scale]

theorem n_lt_scale (B : GrimmettMarstrandBlock d) : B.n < B.scale := by
  simp [scale]

theorem scale_pos (B : GrimmettMarstrandBlock d) : 0 < B.scale := by
  simp [scale]

end GrimmettMarstrandBlock

/-- Center `4Nx` of the site-box indexed by `x`. -/
def grimmettMarstrandSiteCenter {d : ℕ} (N : ℕ) (x : Cubic d) : Cubic d :=
  cubicScale (4 * (N : ℤ)) x

theorem grimmettMarstrandSiteCenter_injective {d N : ℕ} (hN : 0 < N) :
    Function.Injective (grimmettMarstrandSiteCenter (d := d) N) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  simp only [grimmettMarstrandSiteCenter, cubicScale] at hi
  have hscale : (4 * (N : ℤ)) ≠ 0 := by positivity
  exact mul_left_cancel₀ hscale hi

/-- Any choice of a physical anchor lying a uniformly bounded distance from its coarse
Grimmett--Marstrand site has finite fibres.  This is the exact geometric property needed to
turn infinitely many accepted coarse sites into infinitely many physical vertices; injectivity
of the random anchor choice is unnecessary. -/
theorem finite_preimage_of_anchor_mem_siteBox
    {d N R : ℕ} {F : Set (Cubic d)} (hN : 0 < N)
    (anchor : F → Cubic d)
    (hanchor : ∀ x : F,
      anchor x ∈ cubicMetricBox d (grimmettMarstrandSiteCenter N x.1) R) (z : Cubic d) :
    (anchor ⁻¹' ({z} : Set (Cubic d))).Finite := by
  let center : F → Cubic d := fun x ↦ grimmettMarstrandSiteCenter N x.1
  apply Set.Finite.of_finite_image
  · apply (cubicMetricBox d z R).finite_toSet.subset
    rintro y ⟨x, hx, rfl⟩
    have hxz : anchor x = z := by simpa using hx
    apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    rw [cubicLInfDist_comm]
    simpa [hxz] using mem_cubicMetricBox_iff_lInfDist_le.mp (hanchor x)
  · intro x _ y _ hxy
    apply Subtype.ext
    exact grimmettMarstrandSiteCenter_injective hN hxy

/-- Site-box `4Nx+B(N)`. -/
noncomputable def grimmettMarstrandSiteBox
    (d N : ℕ) (x : Cubic d) : Finset (Cubic d) :=
  cubicMetricBox d (grimmettMarstrandSiteCenter N x) N

/-- Midpoint `2N(x+y)` of the site-boxes indexed by adjacent vertices `x,y`. -/
def grimmettMarstrandBondCenter {d : ℕ}
    (N : ℕ) (x y : Cubic d) : Cubic d :=
  fun i => (2 * (N : ℤ)) * (x i + y i)

/-- Bond-box joining two site-boxes.  For adjacent `x,y` this is the source's `Nz+B(N)` with
exactly one coordinate of `z` not divisible by four. -/
noncomputable def grimmettMarstrandBondBox
    (d N : ℕ) (x y : Cubic d) : Finset (Cubic d) :=
  cubicMetricBox d (grimmettMarstrandBondCenter N x y) N

/-- Half-way box in a signed coordinate direction from the site indexed by `x`. -/
noncomputable def grimmettMarstrandHalfwayBox
    (d N : ℕ) (x : Cubic d) (a : CubicDirection d) : Finset (Cubic d) :=
  grimmettMarstrandBondBox d N x (cubicStepFrom x a)

/-- The midpoint of a signed coarse bond is at `L∞` distance exactly at most `2N` from
the destination site center. -/
theorem grimmettMarstrandBondCenter_mem_destinationBox
    {d N : ℕ} (x : Cubic d) (a : CubicDirection d) :
    grimmettMarstrandBondCenter N x (cubicStepFrom x a) ∈
      cubicMetricBox d
        (grimmettMarstrandSiteCenter N (cubicStepFrom x a)) (2 * N) := by
  rw [mem_cubicMetricBox]
  intro i
  rcases a with ⟨j, positive⟩
  by_cases hij : i = j
  · subst i
    by_cases hp : positive <;>
      simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
        cubicStepFrom, cubicDirectionIncrement, hp] <;>
      ring_nf <;> omega
  · simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicScale,
      cubicStepFrom, cubicDirectionIncrement, hij]
    ring_nf
    omega

/-- A half-way seed is uniformly local to the destination coarse site.  The radius is `3N`:
the bond box has radius `N` and its midpoint is `2N` from either endpoint site center. -/
theorem grimmettMarstrandHalfwayBox_subset_destinationBox
    {d N : ℕ} (x : Cubic d) (a : CubicDirection d) :
    (grimmettMarstrandHalfwayBox d N x a : Set (Cubic d)) ⊆
      cubicMetricBox d
        (grimmettMarstrandSiteCenter N (cubicStepFrom x a)) (3 * N) := by
  intro z hz
  apply mem_cubicMetricBox_iff_lInfDist_le.mpr
  rw [cubicLInfDist_comm]
  change z ∈ cubicMetricBox d
    (grimmettMarstrandBondCenter N x (cubicStepFrom x a)) N at hz
  have hzCenter : cubicLInfDist z
      (grimmettMarstrandBondCenter N x (cubicStepFrom x a)) ≤ N := by
    rw [cubicLInfDist_comm]
    exact mem_cubicMetricBox_iff_lInfDist_le.mp hz
  have hcenterDestination : cubicLInfDist
      (grimmettMarstrandBondCenter N x (cubicStepFrom x a))
      (grimmettMarstrandSiteCenter N (cubicStepFrom x a)) ≤ 2 * N := by
    rw [cubicLInfDist_comm]
    exact mem_cubicMetricBox_iff_lInfDist_le.mp
      (grimmettMarstrandBondCenter_mem_destinationBox x a)
  calc
    cubicLInfDist z (grimmettMarstrandSiteCenter N (cubicStepFrom x a)) ≤
        cubicLInfDist z (grimmettMarstrandBondCenter N x (cubicStepFrom x a)) +
          cubicLInfDist (grimmettMarstrandBondCenter N x (cubicStepFrom x a))
            (grimmettMarstrandSiteCenter N (cubicStepFrom x a)) :=
      cubicLInfDist_triangle _ _ _
    _ ≤ N + 2 * N := Nat.add_le_add hzCenter hcenterDestination
    _ = 3 * N := by omega

/-- The final enlarged region `4NF+B(2N)`, written using the literal Chapter 7 thickening. -/
def grimmettMarstrandThickening
    (d : ℕ) (F : Set (Cubic d)) (N : ℕ) : Set (Cubic d) :=
  cubicDilatedThickening d F (2 * N)

theorem grimmettMarstrandSiteCenter_eq_thickeningCenter
    {d N : ℕ} (x : Cubic d) :
    grimmettMarstrandSiteCenter N x = cubicScale (2 * ((2 * N : ℕ) : ℤ)) x := by
  funext i
  change (4 * (N : ℤ)) * x i = (2 * ((2 * N : ℕ) : ℤ)) * x i
  have hcast : ((2 * N : ℕ) : ℤ) = 2 * (N : ℤ) := by norm_num
  rw [hcast]
  ring

theorem grimmettMarstrandSiteBox_subset_thickening
    {d N : ℕ} {F : Set (Cubic d)} {x : Cubic d} (hxF : x ∈ F) :
    (grimmettMarstrandSiteBox d N x : Set (Cubic d)) ⊆
      grimmettMarstrandThickening d F N := by
  intro z hz
  refine ⟨x, hxF, ?_⟩
  rw [← grimmettMarstrandSiteCenter_eq_thickeningCenter]
  change z ∈ cubicMetricBox d (grimmettMarstrandSiteCenter N x) N at hz
  rw [mem_cubicMetricBox] at hz ⊢
  intro i
  have hi := hz i
  omega

/-- Every radius-`2N` box about a coarse site center lies in the final thickening.  The
radius-`N` site-box theorem above is the most common special case; selected restart anchors
need the slightly wider form. -/
theorem grimmettMarstrandCenteredBox_subset_thickening
    {d N R : ℕ} {F : Set (Cubic d)} {x : Cubic d} (hxF : x ∈ F)
    (hR : R ≤ 2 * N) :
    (cubicMetricBox d (grimmettMarstrandSiteCenter N x) R : Set (Cubic d)) ⊆
      grimmettMarstrandThickening d F N := by
  intro z hz
  refine ⟨x, hxF, ?_⟩
  rw [← grimmettMarstrandSiteCenter_eq_thickeningCenter]
  exact mem_cubicMetricBox_iff_lInfDist_le.mpr
    ((mem_cubicMetricBox_iff_lInfDist_le.mp hz).trans hR)

/-- A half-way box is covered by the two radius-`2N` boxes centered at its adjacent site
indices.  This is the exact coordinate fact behind the final `4NF+B(2N)` containment. -/
theorem grimmettMarstrandHalfwayBox_subset_endpointBoxes
    {d N : ℕ} (x : Cubic d) (a : CubicDirection d) :
    (grimmettMarstrandHalfwayBox d N x a : Set (Cubic d)) ⊆
      (cubicMetricBox d (grimmettMarstrandSiteCenter N x) (2 * N) : Set (Cubic d)) ∪
        (cubicMetricBox d (grimmettMarstrandSiteCenter N (cubicStepFrom x a)) (2 * N) :
          Set (Cubic d)) := by
  intro z hz
  rcases a with ⟨j, positive⟩
  have hzBox := mem_cubicMetricBox.mp hz
  by_cases hp : positive
  · by_cases hleft : z j ≤ grimmettMarstrandSiteCenter N x j + 2 * (N : ℤ)
    · left
      change z ∈ cubicMetricBox d (grimmettMarstrandSiteCenter N x) (2 * N)
      rw [mem_cubicMetricBox]
      intro i
      have hi := hzBox i
      by_cases hij : i = j
      · subst i
        simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp] at hi hleft ⊢
        ring_nf at hi hleft ⊢
        omega
      · simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp, hij] at hi ⊢
        ring_nf at hi ⊢
        omega
    · right
      change z ∈ cubicMetricBox d
        (grimmettMarstrandSiteCenter N (cubicStepFrom x (j, positive))) (2 * N)
      rw [mem_cubicMetricBox]
      intro i
      have hi := hzBox i
      by_cases hij : i = j
      · subst i
        simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp] at hi hleft ⊢
        ring_nf at hi hleft ⊢
        omega
      · simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp, hij] at hi ⊢
        ring_nf at hi ⊢
        omega
  · by_cases hleft : grimmettMarstrandSiteCenter N x j - 2 * (N : ℤ) ≤ z j
    · left
      change z ∈ cubicMetricBox d (grimmettMarstrandSiteCenter N x) (2 * N)
      rw [mem_cubicMetricBox]
      intro i
      have hi := hzBox i
      by_cases hij : i = j
      · subst i
        simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp] at hi hleft ⊢
        ring_nf at hi hleft ⊢
        omega
      · simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp, hij] at hi ⊢
        ring_nf at hi ⊢
        omega
    · right
      change z ∈ cubicMetricBox d
        (grimmettMarstrandSiteCenter N (cubicStepFrom x (j, positive))) (2 * N)
      rw [mem_cubicMetricBox]
      intro i
      have hi := hzBox i
      by_cases hij : i = j
      · subst i
        simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp] at hi hleft ⊢
        ring_nf at hi hleft ⊢
        omega
      · simp [grimmettMarstrandBondCenter, grimmettMarstrandSiteCenter, cubicStepFrom,
          cubicScale, cubicDirectionIncrement, hp, hij] at hi ⊢
        ring_nf at hi ⊢
        omega

theorem grimmettMarstrandHalfwayBox_subset_thickening
    {d N : ℕ} {F : Set (Cubic d)} {x : Cubic d} {a : CubicDirection d}
    (hxF : x ∈ F) (hstepF : cubicStepFrom x a ∈ F) :
    (grimmettMarstrandHalfwayBox d N x a : Set (Cubic d)) ⊆
      grimmettMarstrandThickening d F N := by
  intro z hz
  rcases grimmettMarstrandHalfwayBox_subset_endpointBoxes x a hz with hz | hz
  · exact ⟨x, hxF, by
      rwa [← grimmettMarstrandSiteCenter_eq_thickeningCenter]⟩
  · exact ⟨cubicStepFrom x a, hstepF, by
      rwa [← grimmettMarstrandSiteCenter_eq_thickeningCenter]⟩

/-- Order-theoretic conclusion once the block exploration has produced percolation in the
literal enlarged region at a density no larger than `p_c(F)+eta`. -/
theorem exists_regionCriticalProbability_thickening_le_add_of_dynamicPercolation
    {d N : ℕ} {F : Set (Cubic d)} {p : I} {eta : ℝ}
    (hp : (p : ℝ) ≤ regionCriticalProbability d F + eta)
    (hpercolates : 0 < regionHasInfiniteClusterProbability d
      (grimmettMarstrandThickening d F N) p) :
    ∃ k : ℕ,
      regionCriticalProbability d (cubicDilatedThickening d F k) ≤
        regionCriticalProbability d F + eta := by
  refine ⟨2 * N, ?_⟩
  exact (regionCriticalProbability_le_of_hasInfiniteClusterProbability_pos
    hpercolates).trans hp

end Percolation
