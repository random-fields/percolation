import Percolation.Planar.TriangularTranslation
import Percolation.Critical.Basic

/-!
# The triangular Peierls probability argument

This file combines translation invariance, finite boundary parity, normalized hexagonal contour
counting, and a summable strict non-backtracking bound.  The result is a standard-only proof
that homogeneous triangular bond percolation occurs at a rational density below one half.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory SimpleGraph
open scoped Sym2 unitInterval Topology

noncomputable section

/-- Union of the open clusters rooted at the first `M + 1` positive-ray vertices. -/
def triangularPositiveRayClusterUnion (ω : TriangularConfiguration) (M : ℕ) :
    Set SquareVertex :=
  ⋃ k : Fin (M + 1),
    triangularOpenClusterFrom ω (triangularPositiveRayPrimalVertex k)

theorem triangularPositiveRayClusterUnion_finite
    {ω : TriangularConfiguration} {M : ℕ}
    (hfinite : ∀ k : Fin (M + 1),
      (triangularOpenClusterFrom ω
        (triangularPositiveRayPrimalVertex k)).Finite) :
    (triangularPositiveRayClusterUnion ω M).Finite := by
  exact Set.finite_iUnion hfinite

theorem triangularPositiveRayPrimalVertex_mem_clusterUnion
    (ω : TriangularConfiguration) {M k : ℕ} (hk : k ≤ M) :
    triangularPositiveRayPrimalVertex k ∈
      triangularPositiveRayClusterUnion ω M := by
  rw [triangularPositiveRayClusterUnion, Set.mem_iUnion]
  let j : Fin (M + 1) := ⟨k, by omega⟩
  refine ⟨j, ?_⟩
  change (triangularOpenGraph ω).Reachable
    (triangularPositiveRayPrimalVertex k) (triangularPositiveRayPrimalVertex k)
  exact SimpleGraph.Reachable.refl _

theorem cubicOrigin_mem_triangularPositiveRayClusterUnion
    (ω : TriangularConfiguration) (M : ℕ) :
    cubicOrigin ∈ triangularPositiveRayClusterUnion ω M := by
  simpa [triangularPositiveRayPrimalVertex, squareVertex, cubicOrigin] using
    triangularPositiveRayPrimalVertex_mem_clusterUnion ω (M := M) (k := 0) (by omega)

/-- A union of full open clusters is closed under every open triangular edge. -/
theorem triangularPositiveRayClusterUnion_closed
    {ω : TriangularConfiguration} {M : ℕ} {x y : SquareVertex}
    (hxy : (triangularOpenGraph ω).Adj x y)
    (hx : x ∈ triangularPositiveRayClusterUnion ω M) :
    y ∈ triangularPositiveRayClusterUnion ω M := by
  rw [triangularPositiveRayClusterUnion, Set.mem_iUnion] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, hk.trans hxy.reachable⟩

/-- If a primal set is closed under its open edges, every dual boundary walk crosses only
closed primal bonds. -/
theorem mem_triangularHexWalkClosedEvent_of_boundary
    {ω : TriangularConfiguration} {C : Set SquareVertex}
    (hclosed : ∀ {x y : SquareVertex}, (triangularOpenGraph ω).Adj x y →
      x ∈ C → y ∈ C)
    {u v : TriangularHexVertex} (w : triangularHexGraph.Walk u v)
    (hboundary : ∀ e ∈ w.edges,
      e ∈ (triangularHexBoundaryGraph C).edgeSet) :
    ω ∈ triangularHexWalkClosedEvent w := by
  change Disjoint (triangularHexWalkCrossedFinset w : Set TriangularEdge) ω
  rw [Set.disjoint_left]
  intro e heCross heOpen
  change e ∈ triangularHexWalkCrossedFinset w at heCross
  rw [triangularHexWalkCrossedFinset, Finset.mem_map] at heCross
  obtain ⟨d, hdWalk, hde⟩ := heCross
  have hdEdge : (d.1 : Sym2 TriangularHexVertex) ∈ w.edges :=
    (mem_triangularHexWalkEdgeFinset_iff w d).mp hdWalk
  have hdBoundary := hboundary d.1 hdEdge
  rw [mem_triangularHexBoundaryGraph_edgeSet_iff] at hdBoundary
  obtain ⟨_hdHex, hdCut⟩ := hdBoundary
  have hcrossed : triangularHexEdgeCrossed d = e := by
    simpa only [triangularHexEdgeCrossedEmbedding] using hde
  rw [hcrossed] at hdCut
  rcases hdCut with ⟨x, hx, y, hy, hxyEdge⟩
  have hxy : triangularGraph.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet]
    simpa [← hxyEdge] using e.property
  have hxyOpen : (triangularOpenGraph ω).Adj x y := by
    refine ⟨hxy, ?_⟩
    have heq :
        (⟨s(x, y), (SimpleGraph.mem_edgeSet triangularGraph).2 hxy⟩ :
          TriangularEdge) = e := by
      apply Subtype.ext
      exact hxyEdge.symm
    simpa [heq] using heOpen
  exact hy (hclosed hxyOpen hx)

/-- Tail event that a normalized all-closed hexagonal cycle has length strictly greater than
`M`. -/
def positiveRayTriangularHexClosedCycleTailEvent (M : ℕ) :
    Set TriangularConfiguration :=
  ⋃ j : ℕ, positiveRayTriangularHexClosedCycleEvent (M + 1 + j)

theorem measurableSet_positiveRayTriangularHexClosedCycleTailEvent (M : ℕ) :
    MeasurableSet (positiveRayTriangularHexClosedCycleTailEvent M) := by
  exact MeasurableSet.iUnion fun j ↦
    measurableSet_positiveRayTriangularHexClosedCycleEvent (M + 1 + j)

/-- If the first `M + 1` ray-rooted clusters are finite, their normalized outer boundary is an
all-closed contour of length greater than `M`. -/
theorem finite_triangularPositiveRayClusterUnion_mem_closedCycleTail
    {ω : TriangularConfiguration} {M : ℕ}
    (hfinite : (triangularPositiveRayClusterUnion ω M).Finite) :
    ω ∈ positiveRayTriangularHexClosedCycleTailEvent M := by
  let C := triangularPositiveRayClusterUnion ω M
  obtain ⟨n, c, hn, hkEdge, hcBoundary⟩ :=
    exists_positiveRayRootedTriangularHexBoundaryCycle hfinite
      (by simpa [C, triangularPositiveRayPrimalVertex, squareVertex, cubicOrigin] using
        cubicOrigin_mem_triangularPositiveRayClusterUnion ω M)
  have hkBoundary : triangularPositiveRayDualEdge (c.1 : ℕ) ∈
      (triangularHexBoundaryGraph C).edgeSet := hcBoundary _ hkEdge
  have hMk : M ≤ (c.1 : ℕ) := by
    by_contra hnot
    have hklt : (c.1 : ℕ) < M := by omega
    rw [mem_triangularHexBoundaryGraph_edgeSet_iff] at hkBoundary
    obtain ⟨_he, hcut⟩ := hkBoundary
    rw [triangularPositiveRayDualEdge_crossed,
      triangularEdgeCuts_cubicStep_iff] at hcut
    have hstep : cubicStepFrom
        (triangularPositiveRayPrimalVertex (c.1 : ℕ)) ((0 : Fin 2), true) =
        triangularPositiveRayPrimalVertex ((c.1 : ℕ) + 1) := by
      ext i
      fin_cases i <;>
        simp [triangularPositiveRayPrimalVertex, squareVertex,
          cubicStepFrom, cubicDirectionIncrement]
    rw [hstep] at hcut
    have hkIn : triangularPositiveRayPrimalVertex (c.1 : ℕ) ∈ C :=
      triangularPositiveRayPrimalVertex_mem_clusterUnion ω (by omega)
    have hksIn : triangularPositiveRayPrimalVertex ((c.1 : ℕ) + 1) ∈ C :=
      triangularPositiveRayPrimalVertex_mem_clusterUnion ω (by omega)
    simp [hkIn, hksIn] at hcut
  have hMn : M < n := hMk.trans_lt c.1.isLt
  rw [positiveRayTriangularHexClosedCycleTailEvent, Set.mem_iUnion]
  refine ⟨n - (M + 1), ?_⟩
  have hnEq : M + 1 + (n - (M + 1)) = n := by omega
  rw [hnEq]
  refine ⟨c, ?_⟩
  exact mem_triangularHexWalkClosedEvent_of_boundary
    (fun {_x _y} hxy hx ↦ triangularPositiveRayClusterUnion_closed hxy hx)
    c.2.1 hcBoundary

/-- Failure of finiteness for the finite cluster union is exactly the finite union of rooted
infinite-cluster events. -/
theorem not_finite_triangularPositiveRayClusterUnion_event (M : ℕ) :
    {ω : TriangularConfiguration |
      ¬(triangularPositiveRayClusterUnion ω M).Finite} =
    ⋃ k : Fin (M + 1),
      {ω | (triangularOpenClusterFrom ω
        (triangularPositiveRayPrimalVertex k)).Infinite} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    apply hnot
    exact triangularPositiveRayClusterUnion_finite fun k ↦ hnone k
  · rintro ⟨k, hk⟩ hfinite
    apply hk
    exact hfinite.subset (Set.subset_iUnion
      (fun j : Fin (M + 1) ↦ triangularOpenClusterFrom ω
        (triangularPositiveRayPrimalVertex j)) k)

/-- If the origin infinite-cluster probability vanishes, every long closed-cycle tail event has
probability one. -/
theorem inhomogeneousTriangularBondMeasure_real_closedCycleTail_eq_one_of_origin_zero
    (p : I)
    (hzero : (inhomogeneousTriangularBondMeasure p p p).real
      {ω | (triangularOpenCluster ω).Infinite} = 0)
    (M : ℕ) :
    (inhomogeneousTriangularBondMeasure p p p).real
      (positiveRayTriangularHexClosedCycleTailEvent M) = 1 := by
  let μ := inhomogeneousTriangularBondMeasure p p p
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, inhomogeneousTriangularBondMeasure]
    infer_instance
  let B : Set TriangularConfiguration :=
    ⋃ k : Fin (M + 1),
      {ω | (triangularOpenClusterFrom ω
        (triangularPositiveRayPrimalVertex k)).Infinite}
  have hrootNull (k : Fin (M + 1)) :
      μ {ω | (triangularOpenClusterFrom ω
        (triangularPositiveRayPrimalVertex k)).Infinite} = 0 := by
    apply (measureReal_eq_zero_iff (μ := μ)).mp
    rw [inhomogeneousTriangularBondMeasure_real_infiniteClusterFrom_eq_origin]
    exact hzero
  have hBnull : μ B = 0 := by
    exact measure_iUnion_null hrootNull
  have hBmeas : MeasurableSet B := by
    exact MeasurableSet.iUnion fun k ↦
      measurableSet_infinite_triangularOpenClusterFrom
        (triangularPositiveRayPrimalVertex k)
  have hgood : μ.real
      {ω | (triangularPositiveRayClusterUnion ω M).Finite} = 1 := by
    have hcompl : {ω : TriangularConfiguration |
        (triangularPositiveRayClusterUnion ω M).Finite} = Bᶜ := by
      dsimp only [B]
      rw [← not_finite_triangularPositiveRayClusterUnion_event M]
      ext ω
      simp
    rw [hcompl, measureReal_compl hBmeas, probReal_univ,
      (measureReal_eq_zero_iff (μ := μ)).mpr hBnull, sub_zero]
  apply le_antisymm measureReal_le_one
  rw [← hgood]
  exact measureReal_mono fun _ hω ↦
    finite_triangularPositiveRayClusterUnion_mem_closedCycleTail hω

/-! ### Summable strict contour bound -/

/-- A rational homogeneous density strictly below one half used for the Peierls estimate. -/
def triangularPeierlsSubhalfDensity : I :=
  ⟨499 / 1000, by norm_num⟩

/-- The geometric ratio obtained from `31 ≤ (199/100)^5` and closed-edge density `501/1000`. -/
def triangularPeierlsGeometricRatio : ℝ :=
  99699 / 100000

/-- A simple summable majorant for the normalized closed-contour probabilities. -/
def triangularPeierlsMajorant (n : ℕ) : ℝ :=
  1536 * n * triangularPeierlsGeometricRatio ^ n

private theorem five_mul_triangularHexStrictBlockCount_le_length (n : ℕ) :
    5 * triangularHexStrictBlockCount n ≤ n := by
  have hdiv := Nat.mul_div_le (n - 1) 5
  unfold triangularHexStrictBlockCount
  omega

private theorem pow_thirtyOne_strictBlockCount_le (n : ℕ) :
    (31 : ℝ) ^ triangularHexStrictBlockCount n ≤
      (199 / 100 : ℝ) ^ n := by
  let b := triangularHexStrictBlockCount n
  have hb : 5 * b ≤ n :=
    five_mul_triangularHexStrictBlockCount_le_length n
  calc
    (31 : ℝ) ^ b ≤ ((199 / 100 : ℝ) ^ 5) ^ b := by
      gcongr
      norm_num
    _ = (199 / 100 : ℝ) ^ (5 * b) := by rw [pow_mul]
    _ ≤ (199 / 100 : ℝ) ^ n := by
      gcongr <;> norm_num

theorem triangularPeierlsMajorant_nonneg (n : ℕ) :
    0 ≤ triangularPeierlsMajorant n := by
  norm_num [triangularPeierlsMajorant, triangularPeierlsGeometricRatio]

theorem summable_triangularPeierlsMajorant :
    Summable triangularPeierlsMajorant := by
  have hrnorm : ‖triangularPeierlsGeometricRatio‖ < 1 := by
    norm_num [triangularPeierlsGeometricRatio, Real.norm_eq_abs, abs_of_nonneg]
  have hbase : Summable (fun n : ℕ ↦
      (n : ℝ) * triangularPeierlsGeometricRatio ^ n) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm)
  have heq : triangularPeierlsMajorant = fun n : ℕ ↦
      1536 * ((n : ℝ) * triangularPeierlsGeometricRatio ^ n) := by
    funext n
    simp only [triangularPeierlsMajorant]
    ring
  rw [heq]
  exact hbase.mul_left 1536

/-- The finite normalized-cycle union bound is controlled by the summable geometric majorant. -/
theorem inhomogeneousTriangularBondMeasure_real_positiveRayClosedCycleEvent_le_majorant
    (n : ℕ) (hn : 3 ≤ n) :
    (inhomogeneousTriangularBondMeasure triangularPeierlsSubhalfDensity
        triangularPeierlsSubhalfDensity triangularPeierlsSubhalfDensity).real
      (positiveRayTriangularHexClosedCycleEvent n) ≤
        triangularPeierlsMajorant n := by
  have hcount := pow_thirtyOne_strictBlockCount_le n
  calc
    (inhomogeneousTriangularBondMeasure triangularPeierlsSubhalfDensity
        triangularPeierlsSubhalfDensity triangularPeierlsSubhalfDensity).real
        (positiveRayTriangularHexClosedCycleEvent n) ≤
      (n * (3 * 31 ^ triangularHexStrictBlockCount n * 512) : ℕ) *
        (1 - (triangularPeierlsSubhalfDensity : ℝ)) ^ n :=
      inhomogeneousTriangularBondMeasure_real_positiveRayClosedCycleEvent_le
        triangularPeierlsSubhalfDensity n hn
    _ = 1536 * (n : ℝ) *
        (31 : ℝ) ^ triangularHexStrictBlockCount n * (501 / 1000 : ℝ) ^ n := by
      norm_num [triangularPeierlsSubhalfDensity]
      push_cast
      ring
    _ ≤ 1536 * (n : ℝ) *
        (199 / 100 : ℝ) ^ n * (501 / 1000 : ℝ) ^ n := by
      gcongr
    _ = 1536 * (n : ℝ) *
        (((199 / 100 : ℝ) * (501 / 1000 : ℝ)) ^ n) := by
      rw [mul_pow]
      ring
    _ = triangularPeierlsMajorant n := by
      norm_num [triangularPeierlsMajorant, triangularPeierlsGeometricRatio]

private theorem measureReal_iUnion_nat_le_tsum_of_le_triangular
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hbsum : Summable b) (hA : ∀ n, μ.real (A n) ≤ b n) :
    μ.real (⋃ n, A n) ≤ ∑' n, b n := by
  have hmeasure : μ (⋃ n, A n) ≤ ∑' n, ENNReal.ofReal (b n) := by
    refine (measure_iUnion_le A).trans (ENNReal.tsum_le_tsum fun n ↦ ?_)
    calc
      μ (A n) = ENNReal.ofReal (μ.real (A n)) := by
        exact (ENNReal.ofReal_toReal (measure_ne_top μ (A n))).symm
      _ ≤ ENNReal.ofReal (b n) := ENNReal.ofReal_le_ofReal (hA n)
  have hfinite : ∑' n, ENNReal.ofReal (b n) ≠ ⊤ :=
    hbsum.tsum_ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)] at hreal
  simpa only [Measure.real, ENNReal.toReal_ofReal (hb _)] using hreal

/-- Countable union bound for the closed-contour tail. -/
theorem inhomogeneousTriangularBondMeasure_real_closedCycleTail_le_tsum_majorant
    (M : ℕ) (hM : 2 ≤ M) :
    (inhomogeneousTriangularBondMeasure triangularPeierlsSubhalfDensity
        triangularPeierlsSubhalfDensity triangularPeierlsSubhalfDensity).real
      (positiveRayTriangularHexClosedCycleTailEvent M) ≤
        ∑' j : ℕ, triangularPeierlsMajorant (j + (M + 1)) := by
  letI : IsProbabilityMeasure
      (inhomogeneousTriangularBondMeasure triangularPeierlsSubhalfDensity
        triangularPeierlsSubhalfDensity triangularPeierlsSubhalfDensity) := by
    dsimp [inhomogeneousTriangularBondMeasure]
    infer_instance
  have hsumShift : Summable
      (fun j ↦ triangularPeierlsMajorant (M + 1 + j)) := by
    simpa only [Nat.add_comm] using
      ((summable_nat_add_iff (f := triangularPeierlsMajorant) (M + 1)).mpr
        summable_triangularPeierlsMajorant)
  rw [positiveRayTriangularHexClosedCycleTailEvent]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    measureReal_iUnion_nat_le_tsum_of_le_triangular
      (inhomogeneousTriangularBondMeasure triangularPeierlsSubhalfDensity
        triangularPeierlsSubhalfDensity triangularPeierlsSubhalfDensity)
      (fun j ↦ positiveRayTriangularHexClosedCycleEvent (M + 1 + j))
      (fun j ↦ triangularPeierlsMajorant (M + 1 + j))
      (fun j ↦ triangularPeierlsMajorant_nonneg _)
      hsumShift
      (fun j ↦
        inhomogeneousTriangularBondMeasure_real_positiveRayClosedCycleEvent_le_majorant
          (M + 1 + j) (by omega))

/-- Standard-only Peierls conclusion at the chosen rational density below one half. -/
theorem inhomogeneousTriangularBondMeasure_real_originInfinite_pos_subhalf :
    0 <
      (inhomogeneousTriangularBondMeasure triangularPeierlsSubhalfDensity
        triangularPeierlsSubhalfDensity triangularPeierlsSubhalfDensity).real
        {ω | (triangularOpenCluster ω).Infinite} := by
  let μ := inhomogeneousTriangularBondMeasure triangularPeierlsSubhalfDensity
    triangularPeierlsSubhalfDensity triangularPeierlsSubhalfDensity
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, inhomogeneousTriangularBondMeasure]
    infer_instance
  by_contra hnot
  have hzero : μ.real {ω | (triangularOpenCluster ω).Infinite} = 0 := by
    exact le_antisymm (le_of_not_gt hnot) measureReal_nonneg
  have hge (K : ℕ) (hK : 3 ≤ K) :
      1 ≤ ∑' j : ℕ, triangularPeierlsMajorant (j + K) := by
    let M := K - 1
    have hM : 2 ≤ M := by omega
    have hone :=
      inhomogeneousTriangularBondMeasure_real_closedCycleTail_eq_one_of_origin_zero
        triangularPeierlsSubhalfDensity hzero M
    have hle :=
      inhomogeneousTriangularBondMeasure_real_closedCycleTail_le_tsum_majorant M hM
    have hMK : M + 1 = K := by omega
    rw [hone, hMK] at hle
    exact hle
  have htend :=
    tendsto_tsum_nat_add_zero_of_summable summable_triangularPeierlsMajorant
  have heventually : ∀ᶠ K : ℕ in atTop,
      (∑' j : ℕ, triangularPeierlsMajorant (j + K)) < 1 :=
    (tendsto_order.1 htend).2 1 zero_lt_one
  obtain ⟨K, hKsmall, hKlarge⟩ :=
    (heventually.and (eventually_ge_atTop 3)).exists
  exact (not_lt_of_ge (hge K hKlarge)) hKsmall

end

end Percolation
