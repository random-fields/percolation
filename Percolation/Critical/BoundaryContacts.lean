import Percolation.Critical.InfiniteClusterZeroOne
import Percolation.Critical.Seeds
import Percolation.Critical.StaticCoalescence

/-!
# Boundary contacts for Grimmett Lemma 7.9

The first step in the seed amplification argument is elementary but logically important: once
the root-free infinite-cluster event has probability one, expanding central boxes meet an
infinite cluster with probability tending to one.  This file packages that approximation before
introducing the finite boundary-contact counts `U(n)` and `V(n)` from pp. 151--152.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

/-- The event that some vertex of the central box `B(m)` belongs to an infinite open cluster. -/
def centralBoxMeetsInfiniteClusterEvent (d m : ℕ) : Set (EdgeConfiguration d) :=
  {omega | ∃ x ∈ cubicMetricBox d cubicOrigin m,
    hasInfiniteOpenClusterFrom d omega x}

theorem measurableSet_centralBoxMeetsInfiniteClusterEvent (d m : ℕ) :
    MeasurableSet (centralBoxMeetsInfiniteClusterEvent d m) := by
  have hrepr : centralBoxMeetsInfiniteClusterEvent d m =
      ⋃ x ∈ cubicMetricBox d cubicOrigin m,
        {omega | hasInfiniteOpenClusterFrom d omega x} := by
    ext omega
    simp [centralBoxMeetsInfiniteClusterEvent]
  rw [hrepr]
  exact (cubicMetricBox d cubicOrigin m).measurableSet_biUnion fun x _hx =>
    measurableSet_hasInfiniteOpenClusterFrom d x

theorem centralBoxMeetsInfiniteClusterEvent_mono {d m n : ℕ} (hmn : m ≤ n) :
    centralBoxMeetsInfiniteClusterEvent d m ⊆ centralBoxMeetsInfiniteClusterEvent d n := by
  rintro omega ⟨x, hx, hinf⟩
  exact ⟨x, mem_cubicMetricBox_iff_lInfDist_le.mpr
    ((mem_cubicMetricBox_iff_lInfDist_le.mp hx).trans hmn), hinf⟩

theorem monotone_centralBoxMeetsInfiniteClusterEvent (d : ℕ) :
    Monotone (centralBoxMeetsInfiniteClusterEvent d) :=
  fun _m _n hmn => centralBoxMeetsInfiniteClusterEvent_mono hmn

/-- Expanding central boxes exhaust the event that some infinite open component exists. -/
theorem iUnion_centralBoxMeetsInfiniteClusterEvent (d : ℕ) :
    (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m) =
      {omega | hasInfiniteOpenClusterInVertices d Set.univ omega} := by
  ext omega
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, x, _hx, hinf⟩
    exact ⟨x, Set.mem_univ x, by
      simpa [cubicOpenClusterWithinVertices_univ, hasInfiniteOpenClusterFrom] using hinf⟩
  · rintro ⟨x, _hx, hinf⟩
    refine ⟨cubicLInfDist cubicOrigin x, x, ?_, ?_⟩
    · exact mem_cubicMetricBox_iff_lInfDist_le.mpr le_rfl
    · simpa [cubicOpenClusterWithinVertices_univ, hasInfiniteOpenClusterFrom] using hinf

/-- If rooted percolation is positive, expanding central boxes meet an infinite cluster with
probability tending to one.  This is the formal version of the first sentence of the proof of
Lemma 7.9. -/
theorem centralBoxMeetsInfiniteCluster_probability_tendsto_one
    (d : ℕ) [NeZero d] (p : I) (htheta : 0 < theta d p) :
    Tendsto
      (fun m : ℕ =>
        (bernoulliBondMeasure d p).real (centralBoxMeetsInfiniteClusterEvent d m))
      atTop (nhds 1) := by
  let mu := bernoulliBondMeasure d p
  have hcont : Tendsto
      (fun m : ℕ => mu (centralBoxMeetsInfiniteClusterEvent d m)) atTop
      (nhds (mu (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m))) :=
    tendsto_measure_iUnion_atTop (μ := mu) (monotone_centralBoxMeetsInfiniteClusterEvent d)
  have hne : mu (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m) ≠ ∞ :=
    measure_ne_top mu _
  have hreal : Tendsto
      (fun m : ℕ => mu.real (centralBoxMeetsInfiniteClusterEvent d m)) atTop
      (nhds (mu.real (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m))) := by
    simpa [Measure.real] using (ENNReal.tendsto_toReal hne).comp hcont
  have hglobal :
      mu.real (⋃ m : ℕ, centralBoxMeetsInfiniteClusterEvent d m) = 1 := by
    rw [iUnion_centralBoxMeetsInfiniteClusterEvent]
    exact regionHasInfiniteClusterProbability_univ_eq_one_of_theta_pos d p htheta
  simpa [hglobal] using hreal

theorem exists_centralBoxMeetsInfiniteCluster_probability_gt
    (d : ℕ) [NeZero d] (p : I) (htheta : 0 < theta d p)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ,
      1 - epsilon <
        (bernoulliBondMeasure d p).real (centralBoxMeetsInfiniteClusterEvent d m) := by
  have hnhds : Set.Ioi (1 - epsilon) ∈ nhds (1 : ℝ) :=
    Ioi_mem_nhds (sub_lt_self 1 hepsilon)
  have heventually :=
    (centralBoxMeetsInfiniteCluster_probability_tendsto_one d p htheta).eventually hnhds
  obtain ⟨m, hm⟩ := eventually_atTop.1 heventually
  exact ⟨m, hm m le_rfl⟩

/-! ## Finite boundary-contact sets -/

/-- Grimmett's `U(n)`: surface vertices of `B(n)` connected inside `B(n)` to the central
box `B(m)`. -/
noncomputable def boxBoundaryContacts
    (d m n : ℕ) (omega : EdgeConfiguration d) : Finset (Cubic d) := by
  classical
  exact (cubicBoxSurface d cubicOrigin n).filter fun y =>
    ∃ x ∈ cubicMetricBox d cubicOrigin m,
      omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y

@[simp]
theorem mem_boxBoundaryContacts_iff {d m n : ℕ} {omega : EdgeConfiguration d}
    {y : Cubic d} :
    y ∈ boxBoundaryContacts d m n omega ↔
      y ∈ cubicBoxSurface d cubicOrigin n ∧
        ∃ x ∈ cubicMetricBox d cubicOrigin m,
          omega ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y := by
  classical
  simp [boxBoundaryContacts]

/-- The contact-count event `|U(n)| < ell`. -/
def boundaryContactCardLtEvent (d m n ell : ℕ) : Set (EdgeConfiguration d) :=
  {omega | (boxBoundaryContacts d m n omega).card < ell}

/-- The complementary event `ell ≤ |U(n)|`. -/
def boundaryContactCardGeEvent (d m n ell : ℕ) : Set (EdgeConfiguration d) :=
  {omega | ell ≤ (boxBoundaryContacts d m n omega).card}

theorem dependsOn_boundaryContactCardLtEvent (d m n ell : ℕ) :
    DependsOn (cubicBoxEdges d cubicOrigin n) (boundaryContactCardLtEvent d m n ell) := by
  classical
  intro omega eta hagree
  have hcontacts : boxBoundaryContacts d m n omega = boxBoundaryContacts d m n eta := by
    ext y
    simp only [mem_boxBoundaryContacts_iff]
    apply and_congr_right
    intro _hy
    apply exists_congr
    intro x
    apply and_congr_right
    intro _hx
    exact dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y hagree
  simp [boundaryContactCardLtEvent, hcontacts]

theorem measurableSet_boundaryContactCardLtEvent (d m n ell : ℕ) :
    MeasurableSet (boundaryContactCardLtEvent d m n ell) :=
  (dependsOn_boundaryContactCardLtEvent d m n ell).measurableSet

theorem boundaryContactCardGeEvent_eq_compl (d m n ell : ℕ) :
    boundaryContactCardGeEvent d m n ell =
      (boundaryContactCardLtEvent d m n ell)ᶜ := by
  ext omega
  simp [boundaryContactCardGeEvent, boundaryContactCardLtEvent]

theorem measurableSet_boundaryContactCardGeEvent (d m n ell : ℕ) :
    MeasurableSet (boundaryContactCardGeEvent d m n ell) := by
  rw [boundaryContactCardGeEvent_eq_compl]
  exact (measurableSet_boundaryContactCardLtEvent d m n ell).compl

/-- An infinite-cluster vertex in `B(m)` supplies at least one contact on every later surface. -/
theorem boxBoundaryContacts_nonempty_of_centralBoxMeetsInfiniteCluster
    {d m n : ℕ} {omega : EdgeConfiguration d} (hmn : m ≤ n)
    (hinf : omega ∈ centralBoxMeetsInfiniteClusterEvent d m) :
    (boxBoundaryContacts d m n omega).Nonempty := by
  obtain ⟨x, hxBox, hxInf⟩ := hinf
  have hxOuter : x ∈ cubicMetricBox d cubicOrigin n :=
    mem_cubicMetricBox_iff_lInfDist_le.mpr
      ((mem_cubicMetricBox_iff_lInfDist_le.mp hxBox).trans hmn)
  have hsurface := hasInfiniteOpenClusterFrom_mem_connectionToBoxSurfaceEvent hxOuter hxInf
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion] at hsurface
  obtain ⟨y, hySurface, hyConnection⟩ := hsurface
  exact ⟨y, mem_boxBoundaryContacts_iff.mpr
    ⟨hySurface, x, hxBox, hyConnection⟩⟩

theorem centralBoxMeetsInfiniteClusterEvent_subset_one_le_contactCard
    {d m n : ℕ} (hmn : m ≤ n) :
    centralBoxMeetsInfiniteClusterEvent d m ⊆
      {omega | 1 ≤ (boxBoundaryContacts d m n omega).card} := by
  intro omega hinf
  exact Finset.one_le_card.mpr
    (boxBoundaryContacts_nonempty_of_centralBoxMeetsInfiniteCluster hmn hinf)

theorem centralBoxMeetsInfiniteCluster_probability_le_one_le_contactCard
    (d : ℕ) (p : I) {m n : ℕ} (hmn : m ≤ n) :
    (bernoulliBondMeasure d p).real (centralBoxMeetsInfiniteClusterEvent d m) ≤
      (bernoulliBondMeasure d p).real (boundaryContactCardGeEvent d m n 1) := by
  exact measureReal_mono
    (centralBoxMeetsInfiniteClusterEvent_subset_one_le_contactCard hmn)
    (measure_ne_top _ _)

end Percolation
