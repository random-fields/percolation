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

/-! ## A finite packing lemma -/

/-- A bounded-overlap finite family contains a large pairwise-disjoint subfamily.  The factor
`B` bounds each closed conflict neighborhood, including the point itself. -/
theorem exists_pairwiseDisjoint_subfamily_card_mul_ge
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (support : alpha → Finset beta) (B : ℕ)
    (hneighborhood : ∀ a ∈ s,
      (s.filter fun b => b = a ∨ ¬Disjoint (support a) (support b)).card ≤ B) :
    ∃ t : Finset alpha, t ⊆ s ∧
      Set.PairwiseDisjoint (t : Set alpha) support ∧ s.card ≤ t.card * B := by
  classical
  let candidates : Finset (Finset alpha) :=
    s.powerset.filter fun t => Set.PairwiseDisjoint (t : Set alpha) support
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨t, htMax⟩ := candidates.exists_maximal hcandidates
  have htCandidate : t ∈ candidates := htMax.1
  have htSub : t ⊆ s := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp htCandidate).1
  have htPair : Set.PairwiseDisjoint (t : Set alpha) support :=
    (Finset.mem_filter.mp htCandidate).2
  let neighborhood : alpha → Finset alpha := fun a =>
    s.filter fun b => b = a ∨ ¬Disjoint (support a) (support b)
  have hcover : s ⊆ t.biUnion neighborhood := by
    intro a ha
    by_contra hnot
    have haNotT : a ∉ t := by
      intro hat
      apply hnot
      rw [Finset.mem_biUnion]
      refine ⟨a, hat, ?_⟩
      simp [neighborhood, ha]
    have haDisjoint : ∀ b ∈ t, b ≠ a → Disjoint (support b) (support a) := by
      intro b hb hba
      by_contra hconflict
      apply hnot
      rw [Finset.mem_biUnion]
      refine ⟨b, hb, ?_⟩
      simp only [neighborhood, Finset.mem_filter]
      refine ⟨ha, Or.inr ?_⟩
      simpa [disjoint_comm] using hconflict
    have hInsertPair : Set.PairwiseDisjoint ((insert a t : Finset alpha) : Set alpha) support := by
      rw [Finset.coe_insert]
      change (insert a (t : Set alpha)).Pairwise
        (fun x y => Disjoint (support x) (support y))
      rw [Set.pairwise_insert_of_symmetric_of_notMem
        (r := fun x y => Disjoint (support x) (support y))
        (fun _x _y hxy => hxy.symm) haNotT]
      refine ⟨htPair, ?_⟩
      intro b hb
      have hba : b ≠ a := by
        intro h
        subst b
        exact haNotT hb
      exact (haDisjoint b hb hba).symm
    have hInsertCandidate : insert a t ∈ candidates := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha htSub), hInsertPair⟩
    have hInsertLe : insert a t ⊆ t := htMax.2 hInsertCandidate (Finset.subset_insert a t)
    exact haNotT (hInsertLe (Finset.mem_insert_self a t))
  refine ⟨t, htSub, htPair, ?_⟩
  calc
    s.card ≤ (t.biUnion neighborhood).card := Finset.card_le_card hcover
    _ ≤ ∑ a ∈ t, (neighborhood a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ t, B := by
      exact Finset.sum_le_sum fun a ha => hneighborhood a (htSub ha)
    _ = t.card * B := by simp

/-! ## Fresh candidate supports -/

/-- The outward edge together with all internal edges of the canonical adjacent seed. -/
noncomputable def canonicalSeedFreshEdges {d : ℕ}
    (i : Fin d) (m n : ℕ) (y : Cubic d) : Finset (CubicEdge d) :=
  insert (cubicStepEdge y (i, true))
    (cubicBoxEdges d (canonicalBoundarySeedCenter i m n y) m)

/-- All fresh edges of a canonical seed candidate are open. -/
def canonicalSeedSuccessEvent {d : ℕ}
    (i : Fin d) (m n : ℕ) (y : Cubic d) : Set (EdgeConfiguration d) :=
  openEdgeSetEvent d (canonicalSeedFreshEdges i m n y)

theorem measurableSet_canonicalSeedSuccessEvent {d : ℕ}
    (i : Fin d) (m n : ℕ) (y : Cubic d) :
    MeasurableSet (canonicalSeedSuccessEvent i m n y) :=
  measurableSet_openEdgeSetEvent d (canonicalSeedFreshEdges i m n y)

theorem measurableSet_canonicalSeedSuccessEvent_edgeCoordinates {d : ℕ}
    (i : Fin d) (m n : ℕ) (y : Cubic d) :
    MeasurableSet[edgeCoordinateMeasurableSpace d (canonicalSeedFreshEdges i m n y)]
      (canonicalSeedSuccessEvent i m n y) :=
  measurableSet_openEdgeSetEvent_edgeCoordinateMeasurableSpace d
    (canonicalSeedFreshEdges i m n y)

/-- A successful canonical candidate attached to a contacted quadrant vertex realizes the
source event (7.10). -/
theorem mem_seedConnectionEvent_of_orthantContact_of_canonicalSeedSuccess
    {d m n : ℕ} (i : Fin d) {y : Cubic d} {omega : EdgeConfiguration d}
    (hmn : 2 * m ≤ n)
    (hy : y ∈ orthantBoundaryContacts d m n (allPositiveBoxSurfaceOrthantIndex i) omega)
    (hsuccess : omega ∈ canonicalSeedSuccessEvent i m n y) :
    omega ∈ seedConnectionEvent d i m n := by
  obtain ⟨hyContact, hyOrthant⟩ := mem_orthantBoundaryContacts_iff.mp hy
  obtain ⟨_hySurface, x, hx, hxy⟩ := mem_boxBoundaryContacts_iff.mp hyContact
  have hyQuadrant : y ∈ seededBoundaryQuadrant d i n := by
    rw [← boxSurfaceOrthant_allPositive_eq_seededBoundaryQuadrant i]
    exact hyOrthant
  have hedge : cubicStepEdge y (i, true) ∈ omega := by
    exact hsuccess (Finset.mem_insert_self _ _)
  have hseed : omega ∈ cubicSeedEvent d (canonicalBoundarySeedCenter i m n y) m := by
    intro e he
    exact hsuccess (Finset.mem_insert_of_mem he)
  exact ⟨x, hx, y,
    isSeededBoundaryPoint_of_canonicalSeed i hmn hyQuadrant hedge hseed, hxy⟩

theorem seededBoundaryLayerRegion_not_mem_innerBox
    {d m n : ℕ} (i : Fin d) {z : Cubic d}
    (hz : z ∈ seededBoundaryLayerRegion d i m n) :
    z ∉ cubicMetricBox d cubicOrigin n := by
  rintro hzBox
  obtain ⟨r, hr1, _hr2, y, hy, rfl⟩ := hz
  have hyFace := (mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hy).1).1
  have hzCoord := mem_cubicMetricBox.mp hzBox i
  simp [cubicTranslateAlongCoordinate, cubicOrigin] at hyFace hzCoord
  omega

/-- The contact history inside `B(n)` is disjoint from every edge used to test its canonical
adjacent seed. -/
theorem disjoint_innerBoxEdges_canonicalSeedFreshEdges
    {d m n : ℕ} (i : Fin d) {y : Cubic d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n) :
    Disjoint (cubicBoxEdges d cubicOrigin n : Set (CubicEdge d))
      (canonicalSeedFreshEdges i m n y : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInner heFresh
  rw [Finset.mem_coe, canonicalSeedFreshEdges, Finset.mem_insert] at heFresh
  rcases heFresh with rfl | heSeed
  · have hstepOutside : cubicStepFrom y (i, true) ∉ cubicMetricBox d cubicOrigin n := by
      rw [mem_cubicMetricBox]
      push Not
      refine ⟨i, ?_⟩
      have hyFace := (mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hy).1).1
      simp [cubicStepFrom, cubicDirectionIncrement, cubicOrigin] at hyFace ⊢
      omega
    exact hstepOutside
      (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heInner (by
        simp [cubicStepEdge]))
  · let z := (e : Sym2 (Cubic d)).out.1
    have hzEndpoint : z ∈ (e : Sym2 (Cubic d)) := Sym2.out_fst_mem _
    have hzSeed : z ∈ cubicMetricBox d (canonicalBoundarySeedCenter i m n y) m :=
      endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heSeed hzEndpoint
    have hzLayer := canonicalBoundarySeedBoxWithinBoundaryLayer i hmn hy z hzSeed
    exact seededBoundaryLayerRegion_not_mem_innerBox i hzLayer
      (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heInner hzEndpoint)

/-- Every endpoint of a fresh canonical candidate lies in a uniformly bounded box around its
contact point. -/
theorem canonicalSeedFreshEdge_endpoint_mem_contactBox
    {d m n : ℕ} (i : Fin d) {y z : Cubic d} {e : CubicEdge d}
    (hmn : 2 * m ≤ n) (hy : y ∈ seededBoundaryQuadrant d i n)
    (he : e ∈ canonicalSeedFreshEdges i m n y) (hz : z ∈ (e : Sym2 (Cubic d))) :
    z ∈ cubicMetricBox d y (2 * m + 1) := by
  rw [canonicalSeedFreshEdges, Finset.mem_insert] at he
  rcases he with rfl | heSeed
  · rw [cubicStepEdge, Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)
    · exact mem_cubicMetricBox_iff_lInfDist_le.mpr
        ((cubicLInfDist_stepFrom_le_one y (i, true)).trans (by omega))
  · have hzSeed : z ∈ cubicMetricBox d (canonicalBoundarySeedCenter i m n y) m :=
      endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heSeed hz
    have hstepSeed := cubicStepFrom_mem_canonicalBoundarySeedBox i hmn hy
    apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    calc
      cubicLInfDist y z ≤
          cubicLInfDist y (cubicStepFrom y (i, true)) +
            cubicLInfDist (cubicStepFrom y (i, true)) z :=
        cubicLInfDist_triangle y (cubicStepFrom y (i, true)) z
      _ ≤ 1 + (m + m) := by
        gcongr
        · exact cubicLInfDist_stepFrom_le_one y (i, true)
        · calc
            cubicLInfDist (cubicStepFrom y (i, true)) z ≤
                cubicLInfDist (cubicStepFrom y (i, true))
                    (canonicalBoundarySeedCenter i m n y) +
                  cubicLInfDist (canonicalBoundarySeedCenter i m n y) z :=
              cubicLInfDist_triangle _ _ _
            _ ≤ m + m := Nat.add_le_add
              (by
                rw [cubicLInfDist_comm]
                exact mem_cubicMetricBox_iff_lInfDist_le.mp hstepSeed)
              (mem_cubicMetricBox_iff_lInfDist_le.mp hzSeed)
      _ = 2 * m + 1 := by omega

/-- Closed conflict neighborhood for the canonical fresh-edge supports. -/
noncomputable def canonicalSeedConflictNeighborhood {d : ℕ}
    (i : Fin d) (m n : ℕ) (S : Finset (Cubic d)) (y : Cubic d) : Finset (Cubic d) :=
  S.filter fun z => z = y ∨
    ¬Disjoint (canonicalSeedFreshEdges i m n y) (canonicalSeedFreshEdges i m n z)

/-- A canonical candidate conflicts with at most `(8m+5)^d` contact points. -/
theorem canonicalSeedConflictNeighborhood_card_le
    {d m n : ℕ} (i : Fin d) (S : Finset (Cubic d))
    (hmn : 2 * m ≤ n)
    (hS : ∀ y ∈ S, y ∈ seededBoundaryQuadrant d i n)
    (y : Cubic d) (hyS : y ∈ S) :
    (canonicalSeedConflictNeighborhood i m n S y).card ≤ (8 * m + 5) ^ d := by
  have hy := hS y hyS
  have hsubset : canonicalSeedConflictNeighborhood i m n S y ⊆
      cubicMetricBox d y (4 * m + 2) := by
    intro z hz
    rw [canonicalSeedConflictNeighborhood, Finset.mem_filter] at hz
    obtain ⟨hzS, hzy⟩ := hz
    rcases hzy with rfl | hconflict
    · exact mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)
    · obtain ⟨e, hey, hez⟩ := Finset.not_disjoint_iff.mp hconflict
      let v := (e : Sym2 (Cubic d)).out.1
      have hv : v ∈ (e : Sym2 (Cubic d)) := Sym2.out_fst_mem _
      have hvy := canonicalSeedFreshEdge_endpoint_mem_contactBox i hmn hy hey hv
      have hvz := canonicalSeedFreshEdge_endpoint_mem_contactBox i hmn (hS z hzS) hez hv
      apply mem_cubicMetricBox_iff_lInfDist_le.mpr
      calc
        cubicLInfDist y z ≤ cubicLInfDist y v + cubicLInfDist v z :=
          cubicLInfDist_triangle y v z
        _ ≤ (2 * m + 1) + (2 * m + 1) := Nat.add_le_add
          (mem_cubicMetricBox_iff_lInfDist_le.mp hvy)
          (by
            rw [cubicLInfDist_comm]
            exact mem_cubicMetricBox_iff_lInfDist_le.mp hvz)
        _ = 4 * m + 2 := by omega
  calc
    (canonicalSeedConflictNeighborhood i m n S y).card ≤
        (cubicMetricBox d y (4 * m + 2)).card := Finset.card_le_card hsubset
    _ = (2 * (4 * m + 2) + 1) ^ d := cubicMetricBox_card d y (4 * m + 2)
    _ = (8 * m + 5) ^ d := by
      congr 1
      omega

/-- Many quadrant contacts yield many candidates whose fresh edge supports are pairwise disjoint. -/
theorem exists_canonicalSeedFreshEdges_pairwiseDisjoint
    {d m n K : ℕ} (i : Fin d) (S : Finset (Cubic d))
    (hmn : 2 * m ≤ n)
    (hS : ∀ y ∈ S, y ∈ seededBoundaryQuadrant d i n)
    (hcard : K * ((8 * m + 5) ^ d) ≤ S.card) :
    ∃ T : Finset (Cubic d), T ⊆ S ∧ K ≤ T.card ∧
      Set.PairwiseDisjoint (T : Set (Cubic d))
        (canonicalSeedFreshEdges i m n) := by
  let B := (8 * m + 5) ^ d
  obtain ⟨T, hTS, hpair, hupper⟩ :=
    exists_pairwiseDisjoint_subfamily_card_mul_ge S
      (canonicalSeedFreshEdges i m n) B (fun y hy => by
        simpa [canonicalSeedConflictNeighborhood] using
          canonicalSeedConflictNeighborhood_card_le i S hmn hS y hy)
  have hmul : K * B ≤ T.card * B := hcard.trans hupper
  have hB : 0 < B := by positivity
  exact ⟨T, hTS, Nat.le_of_mul_le_mul_right hmul hB, hpair⟩

/-! ## Independent finite open blocks -/

theorem cubicBoxEdges_card_le (d : ℕ) (x : Cubic d) (m : ℕ) :
    (cubicBoxEdges d x m).card ≤ (2 * m + 1) ^ d * (2 * d) := by
  classical
  let directionsAt : Cubic d → Finset (CubicEdge d) := fun y =>
    ((Finset.univ.filter fun a : CubicDirection d =>
      cubicStepFrom y a ∈ cubicMetricBox d x m).image fun a => cubicStepEdge y a)
  have hdir : ∀ y, (directionsAt y).card ≤ 2 * d := by
    intro y
    calc
      (directionsAt y).card ≤
          (Finset.univ.filter fun a : CubicDirection d =>
            cubicStepFrom y a ∈ cubicMetricBox d x m).card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (CubicDirection d)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 * d := by simp [CubicDirection, Nat.mul_comm]
  change ((cubicMetricBox d x m).biUnion directionsAt).card ≤ _
  calc
    ((cubicMetricBox d x m).biUnion directionsAt).card ≤
        ∑ y ∈ cubicMetricBox d x m, (directionsAt y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ cubicMetricBox d x m, 2 * d := by
      exact Finset.sum_le_sum fun y _hy => hdir y
    _ = (2 * m + 1) ^ d * (2 * d) := by
      rw [← cubicMetricBox_card d x m]
      simp

/-- Uniform size bound for every canonical candidate support. -/
theorem canonicalSeedFreshEdges_card_le
    {d m n : ℕ} (i : Fin d) (y : Cubic d) :
    (canonicalSeedFreshEdges i m n y).card ≤
      1 + (2 * m + 1) ^ d * (2 * d) := by
  calc
    (canonicalSeedFreshEdges i m n y).card ≤
        1 + (cubicBoxEdges d (canonicalBoundarySeedCenter i m n y) m).card := by
      simpa [canonicalSeedFreshEdges, Nat.add_comm] using
        Finset.card_insert_le (cubicStepEdge y (i, true))
          (cubicBoxEdges d (canonicalBoundarySeedCenter i m n y) m)
    _ ≤ 1 + (2 * m + 1) ^ d * (2 * d) :=
      Nat.add_le_add_left (cubicBoxEdges_card_le d _ m) 1

/-- Open-edge events on a pairwise-disjoint family of finite supports are mutually independent. -/
theorem bernoulliBondMeasure_iIndepSet_openEdgeSetEvent_of_pairwiseDisjoint
    {d : ℕ} {kappa : Type*} [DecidableEq kappa]
    (p : I) (support : kappa → Finset (CubicEdge d))
    (hpair : Set.PairwiseDisjoint (Set.univ : Set kappa) support) :
    iIndepSet (fun k => openEdgeSetEvent d (support k)) (bernoulliBondMeasure d p) := by
  classical
  apply (iIndepSet_iff_meas_biInter
    (fun k => measurableSet_openEdgeSetEvent d (support k))).2
  intro J
  have hJ : (J : Set kappa).PairwiseDisjoint support :=
    hpair.subset (Set.subset_univ _)
  have hinter : (⋂ k ∈ J, openEdgeSetEvent d (support k)) =
      openEdgeSetEvent d (J.biUnion support) := by
    ext omega
    simp only [Set.mem_iInter, Set.mem_setOf_eq,
      openEdgeSetEvent, Finset.coe_biUnion, Set.iUnion_subset_iff]
    constructor
    · intro h k hk e he
      exact h k hk he
    · intro h k hk e he
      exact h k (by simpa using hk) he
  have hleft_ne_top :
      (bernoulliBondMeasure d p) (⋂ k ∈ J, openEdgeSetEvent d (support k)) ≠ ⊤ := by
    refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top
  have hright_ne_top :
      (∏ k ∈ J, (bernoulliBondMeasure d p) (openEdgeSetEvent d (support k))) ≠ ⊤ :=
    ENNReal.prod_ne_top fun k _hk => by
      refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top
  rw [← ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top]
  rw [ENNReal.toReal_prod]
  change (bernoulliBondMeasure d p).real
      (⋂ k ∈ J, openEdgeSetEvent d (support k)) =
    ∏ k ∈ J, (bernoulliBondMeasure d p).real (openEdgeSetEvent d (support k))
  rw [hinter, bernoulliBondMeasure_real_openEdgeSetEvent,
    Finset.card_biUnion hJ]
  simp_rw [bernoulliBondMeasure_real_openEdgeSetEvent]
  exact (Finset.prod_pow_eq_pow_sum J
    (fun k => (support k).card) (p : ℝ)).symm

/-- Mutual independence is unchanged when every event is complemented. -/
theorem iIndepSet_compl {Omega kappa : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A : kappa → Set Omega} (hA : iIndepSet A mu) :
    iIndepSet (fun k => (A k)ᶜ) mu := by
  rw [iIndepSet_iff_iIndep] at hA ⊢
  have hgen : ∀ k,
      MeasurableSpace.generateFrom {(A k)ᶜ} = MeasurableSpace.generateFrom {A k} := by
    intro k
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst s
      exact (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl
    · apply MeasurableSpace.generateFrom_le
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst s
      have hcompl : MeasurableSet[MeasurableSpace.generateFrom {(A k)ᶜ}] ((A k)ᶜ) :=
        MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
      simpa only [compl_compl] using hcompl.compl
  convert hA using 1
  funext k
  exact hgen k

/-- Uniform success probability of one fresh canonical seed candidate. -/
theorem canonicalSeedSuccess_probability_ge
    {d m n : ℕ} (p : I) (i : Fin d) (y : Cubic d) :
    (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d)) ≤
      (bernoulliBondMeasure d p).real (canonicalSeedSuccessEvent i m n y) := by
  rw [canonicalSeedSuccessEvent, bernoulliBondMeasure_real_openEdgeSetEvent]
  exact pow_le_pow_of_le_one p.2.1 p.2.2
    (canonicalSeedFreshEdges_card_le i y)

/-- Failure of all candidates in a pairwise-disjoint finite packing has geometric probability. -/
theorem canonicalSeedFailure_probability_le_pow
    {d m n : ℕ} (p : I) (i : Fin d) (T : Finset (Cubic d))
    (hpair : Set.PairwiseDisjoint (T : Set (Cubic d))
      (canonicalSeedFreshEdges i m n)) :
    (bernoulliBondMeasure d p).real
        (⋂ y : {y : Cubic d // y ∈ T},
          (canonicalSeedSuccessEvent i m n y.1)ᶜ) ≤
      (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ T.card := by
  classical
  let success : {y : Cubic d // y ∈ T} → Set (EdgeConfiguration d) := fun y =>
    canonicalSeedSuccessEvent i m n y.1
  have hpairSubtype : Set.PairwiseDisjoint
      (Set.univ : Set {y : Cubic d // y ∈ T})
      (fun y => canonicalSeedFreshEdges i m n y.1) := by
    intro a _ha b _hb hab
    exact hpair a.2 b.2 (fun h => hab (Subtype.ext h))
  have hiOpen : iIndepSet success (bernoulliBondMeasure d p) := by
    have hiRaw :=
      bernoulliBondMeasure_iIndepSet_openEdgeSetEvent_of_pairwiseDisjoint
        (d := d) (kappa := {y : Cubic d // y ∈ T}) p
        (fun y => canonicalSeedFreshEdges i m n y.1) hpairSubtype
    simpa [success, canonicalSeedSuccessEvent] using hiRaw
  have hiFail : iIndepSet (fun y => (success y)ᶜ) (bernoulliBondMeasure d p) :=
    iIndepSet_compl hiOpen
  have hmeasure := hiFail.meas_biInter (Finset.univ : Finset {y : Cubic d // y ∈ T})
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_prod] at hreal
  have hfactor : ∀ y : {y : Cubic d // y ∈ T},
      (bernoulliBondMeasure d p).real ((success y)ᶜ) ≤
        1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d)) := by
    intro y
    rw [probReal_compl_eq_one_sub (measurableSet_canonicalSeedSuccessEvent i m n y.1)]
    linarith [canonicalSeedSuccess_probability_ge (m := m) (n := n) p i y.1]
  calc
    (bernoulliBondMeasure d p).real
        (⋂ y : {y : Cubic d // y ∈ T},
          (canonicalSeedSuccessEvent i m n y.1)ᶜ) =
      ∏ y : {y : Cubic d // y ∈ T},
        (bernoulliBondMeasure d p).real ((success y)ᶜ) := by
          simpa [success] using hreal
    _ ≤ ∏ _y : {y : Cubic d // y ∈ T},
        (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) := by
      exact Finset.prod_le_prod (fun _ _ => by positivity) (fun y _hy => hfactor y)
    _ = (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ T.card := by
      simp

/-! ## Exact quadrant-contact histories -/

def orthantBoundaryContactSetEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (S : Finset (Cubic d)) :
    Set (EdgeConfiguration d) :=
  {omega | orthantBoundaryContacts d m n a omega = S}

theorem dependsOn_orthantBoundaryContactSetEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (S : Finset (Cubic d)) :
    DependsOn (cubicBoxEdges d cubicOrigin n)
      (orthantBoundaryContactSetEvent d m n a S) := by
  classical
  intro omega eta hagree
  have hcontacts : orthantBoundaryContacts d m n a omega =
      orthantBoundaryContacts d m n a eta := by
    ext y
    simp only [mem_orthantBoundaryContacts_iff, mem_boxBoundaryContacts_iff]
    apply and_congr
    · apply and_congr_right
      intro _hySurface
      apply exists_congr
      intro x
      apply and_congr_right
      intro _hx
      exact dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y hagree
    · rfl
  simp [orthantBoundaryContactSetEvent, hcontacts]

theorem measurableSet_orthantBoundaryContactSetEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (S : Finset (Cubic d)) :
    MeasurableSet (orthantBoundaryContactSetEvent d m n a S) :=
  (dependsOn_orthantBoundaryContactSetEvent d m n a S).measurableSet

theorem measurableSet_orthantBoundaryContactSetEvent_edgeCoordinates
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (S : Finset (Cubic d)) :
    MeasurableSet[edgeCoordinateMeasurableSpace d (cubicBoxEdges d cubicOrigin n)]
      (orthantBoundaryContactSetEvent d m n a S) := by
  simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
    (dependsOn_orthantBoundaryContactSetEvent d m n a S).measurableSet_generateFrom_coordinateEvents
      (S := (cubicBoxEdges d cubicOrigin n : Set (CubicEdge d))) (by simp)

noncomputable def largeOrthantBoundaryContactSets
    (d n : ℕ) (a : BoxSurfaceOrthantIndex d) (ell : ℕ) :
    Finset (Finset (Cubic d)) :=
  (boxSurfaceOrthant d n a).powerset.filter fun S => ell ≤ S.card

theorem mem_largeOrthantBoundaryContactSets_iff
    {d n ell : ℕ} {a : BoxSurfaceOrthantIndex d} {S : Finset (Cubic d)} :
    S ∈ largeOrthantBoundaryContactSets d n a ell ↔
      S ⊆ boxSurfaceOrthant d n a ∧ ell ≤ S.card := by
  classical
  simp [largeOrthantBoundaryContactSets]

theorem orthantBoundaryContactCardGeEvent_eq_biUnion_contactSet
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (ell : ℕ) :
    orthantBoundaryContactCardGeEvent d m n a ell =
      ⋃ S ∈ largeOrthantBoundaryContactSets d n a ell,
        orthantBoundaryContactSetEvent d m n a S := by
  classical
  ext omega
  simp only [orthantBoundaryContactCardGeEvent, Set.mem_setOf_eq,
    Set.mem_iUnion, orthantBoundaryContactSetEvent]
  constructor
  · intro hcard
    let S := orthantBoundaryContacts d m n a omega
    have hsubset : S ⊆ boxSurfaceOrthant d n a := by
      intro y hy
      exact (mem_orthantBoundaryContacts_iff.mp hy).2
    exact ⟨S, mem_largeOrthantBoundaryContactSets_iff.mpr ⟨hsubset, hcard⟩, rfl⟩
  · rintro ⟨S, hS, hEq⟩
    rw [hEq]
    exact (mem_largeOrthantBoundaryContactSets_iff.mp hS).2

theorem pairwiseDisjoint_orthantBoundaryContactSetEvent
    (d m n : ℕ) (a : BoxSurfaceOrthantIndex d) (ell : ℕ) :
    Set.PairwiseDisjoint
      (largeOrthantBoundaryContactSets d n a ell : Set (Finset (Cubic d)))
      (orthantBoundaryContactSetEvent d m n a) := by
  intro S _hS T _hT hST
  change Disjoint (orthantBoundaryContactSetEvent d m n a S)
    (orthantBoundaryContactSetEvent d m n a T)
  rw [Set.disjoint_left]
  intro omega hS hT
  exact hST (hS.symm.trans hT)

theorem dependsOn_canonicalSeedSuccessEvent {d : ℕ}
    (i : Fin d) (m n : ℕ) (y : Cubic d) :
    DependsOn (canonicalSeedFreshEdges i m n y)
      (canonicalSeedSuccessEvent i m n y) := by
  intro omega eta hagree
  constructor
  · intro homega e he
    exact (hagree e he).mp (homega he)
  · intro heta e he
    exact (hagree e he).mpr (heta he)

theorem dependsOn_canonicalSeedFailureEvent
    {d : ℕ} (i : Fin d) (m n : ℕ) (T : Finset (Cubic d)) :
    DependsOn (T.biUnion (canonicalSeedFreshEdges i m n))
      (⋂ y ∈ T, (canonicalSeedSuccessEvent i m n y)ᶜ) := by
  apply dependsOn_biInter
  intro y hy
  exact (dependsOn_canonicalSeedSuccessEvent i m n y).compl

theorem measurableSet_canonicalSeedFailureEvent_edgeCoordinates
    {d : ℕ} (i : Fin d) (m n : ℕ) (T : Finset (Cubic d)) :
    MeasurableSet[edgeCoordinateMeasurableSpace d
        (T.biUnion (canonicalSeedFreshEdges i m n))]
      (⋂ y ∈ T, (canonicalSeedSuccessEvent i m n y)ᶜ) := by
  simpa [edgeCoordinateMeasurableSpace, edgeCoordinateEvents] using
    (dependsOn_canonicalSeedFailureEvent i m n T).measurableSet_generateFrom_coordinateEvents
      (S := (T.biUnion (canonicalSeedFreshEdges i m n) : Set (CubicEdge d))) (by simp)

theorem disjoint_innerBoxEdges_biUnion_canonicalSeedFreshEdges
    {d m n : ℕ} (i : Fin d) (T : Finset (Cubic d))
    (hmn : 2 * m ≤ n) (hT : ∀ y ∈ T, y ∈ seededBoundaryQuadrant d i n) :
    Disjoint (cubicBoxEdges d cubicOrigin n : Set (CubicEdge d))
      (T.biUnion (canonicalSeedFreshEdges i m n) : Set (CubicEdge d)) := by
  rw [Set.disjoint_left]
  intro e heInner heFresh
  rw [Finset.mem_coe, Finset.mem_biUnion] at heFresh
  obtain ⟨y, hyT, hey⟩ := heFresh
  exact Set.disjoint_left.mp
    (disjoint_innerBoxEdges_canonicalSeedFreshEdges i hmn (hT y hyT)) heInner hey

theorem orthantBoundaryContactSetEvent_indep_canonicalSeedFailureEvent
    {d m n : ℕ} (p : I) (i : Fin d) (S T : Finset (Cubic d))
    (hmn : 2 * m ≤ n) (hT : ∀ y ∈ T, y ∈ seededBoundaryQuadrant d i n) :
    IndepSet
      (orthantBoundaryContactSetEvent d m n (allPositiveBoxSurfaceOrthantIndex i) S)
      (⋂ y ∈ T, (canonicalSeedSuccessEvent i m n y)ᶜ)
      (bernoulliBondMeasure d p) := by
  exact bernoulliBondMeasure_indepSet_of_measurableSet_edgeCoordinateMeasurableSpace
    d p (cubicBoxEdges d cubicOrigin n)
      (T.biUnion (canonicalSeedFreshEdges i m n))
    (disjoint_innerBoxEdges_biUnion_canonicalSeedFreshEdges i T hmn hT)
    (measurableSet_orthantBoundaryContactSetEvent_edgeCoordinates d m n
      (allPositiveBoxSurfaceOrthantIndex i) S)
    (measurableSet_canonicalSeedFailureEvent_edgeCoordinates i m n T)

theorem canonicalSeedFailureEvent_eq_subtype_iInter
    {d m n : ℕ} (i : Fin d) (T : Finset (Cubic d)) :
    (⋂ y ∈ T, (canonicalSeedSuccessEvent i m n y)ᶜ) =
      ⋂ y : {y : Cubic d // y ∈ T},
        (canonicalSeedSuccessEvent i m n y.1)ᶜ := by
  ext omega
  simp

/-- On an exact large quadrant-contact history, failure to realize (7.10) costs a uniform
geometric factor. -/
theorem orthantContactSet_inter_seedConnection_compl_probability_le
    {d m n K : ℕ} (p : I) (i : Fin d) (S : Finset (Cubic d))
    (hmn : 2 * m ≤ n)
    (hSsubset : S ⊆ boxSurfaceOrthant d n (allPositiveBoxSurfaceOrthantIndex i))
    (hScard : K * ((8 * m + 5) ^ d) ≤ S.card) :
    (bernoulliBondMeasure d p).real
        (orthantBoundaryContactSetEvent d m n (allPositiveBoxSurfaceOrthantIndex i) S ∩
          (seedConnectionEvent d i m n)ᶜ) ≤
      (bernoulliBondMeasure d p).real
          (orthantBoundaryContactSetEvent d m n (allPositiveBoxSurfaceOrthantIndex i) S) *
        (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ K := by
  classical
  have hSquadrant : ∀ y ∈ S, y ∈ seededBoundaryQuadrant d i n := by
    intro y hy
    rw [← boxSurfaceOrthant_allPositive_eq_seededBoundaryQuadrant i]
    exact hSsubset hy
  obtain ⟨T, hTS, hKT, hpair⟩ :=
    exists_canonicalSeedFreshEdges_pairwiseDisjoint i S hmn hSquadrant hScard
  have hTquadrant : ∀ y ∈ T, y ∈ seededBoundaryQuadrant d i n := by
    intro y hy
    exact hSquadrant y (hTS hy)
  let history :=
    orthantBoundaryContactSetEvent d m n (allPositiveBoxSurfaceOrthantIndex i) S
  let failure := ⋂ y ∈ T, (canonicalSeedSuccessEvent i m n y)ᶜ
  have hsubset : history ∩ (seedConnectionEvent d i m n)ᶜ ⊆ history ∩ failure := by
    intro omega homega
    refine ⟨homega.1, ?_⟩
    simp only [failure, Set.mem_iInter]
    intro y hyT hsuccess
    apply homega.2
    apply mem_seedConnectionEvent_of_orthantContact_of_canonicalSeedSuccess i hmn
    · have hhistory : orthantBoundaryContacts d m n
          (allPositiveBoxSurfaceOrthantIndex i) omega = S := homega.1
      rw [hhistory]
      exact hTS hyT
    · exact hsuccess
  have hind := orthantBoundaryContactSetEvent_indep_canonicalSeedFailureEvent
    p i S T hmn hTquadrant
  have hproduct :
      (bernoulliBondMeasure d p).real (history ∩ failure) =
        (bernoulliBondMeasure d p).real history *
          (bernoulliBondMeasure d p).real failure := by
    have hmeasure := hind.measure_inter_eq_mul
    have hreal := congrArg ENNReal.toReal hmeasure
    rw [ENNReal.toReal_mul, ← Measure.real, ← Measure.real] at hreal
    exact hreal
  have hfailure :
      (bernoulliBondMeasure d p).real failure ≤
        (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ T.card := by
    dsimp [failure]
    rw [canonicalSeedFailureEvent_eq_subtype_iInter]
    exact canonicalSeedFailure_probability_le_pow p i T hpair
  have hqNonneg :
      0 ≤ 1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d)) := by
    have hpPow : (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d)) ≤ 1 := by
      exact pow_le_one₀ p.2.1 p.2.2
    linarith
  have hqLeOne :
      1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d)) ≤ 1 :=
    sub_le_self 1 (pow_nonneg p.2.1 _)
  have hpow :
      (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ T.card ≤
        (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ K :=
    pow_le_pow_of_le_one hqNonneg hqLeOne hKT
  calc
    (bernoulliBondMeasure d p).real
        (history ∩ (seedConnectionEvent d i m n)ᶜ) ≤
      (bernoulliBondMeasure d p).real (history ∩ failure) :=
        measureReal_mono hsubset (measure_ne_top _ _)
    _ = (bernoulliBondMeasure d p).real history *
        (bernoulliBondMeasure d p).real failure := hproduct
    _ ≤ (bernoulliBondMeasure d p).real history *
        (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ T.card :=
      mul_le_mul_of_nonneg_left hfailure measureReal_nonneg
    _ ≤ (bernoulliBondMeasure d p).real history *
        (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ K :=
      mul_le_mul_of_nonneg_left hpow measureReal_nonneg

/-- Large quadrant contact count amplifies into a seeded connection, with an explicit geometric
failure factor. -/
theorem orthantContactGe_inter_seedConnection_compl_probability_le
    {d m n K : ℕ} (p : I) (i : Fin d) (hmn : 2 * m ≤ n) :
    (bernoulliBondMeasure d p).real
        (orthantBoundaryContactCardGeEvent d m n
            (allPositiveBoxSurfaceOrthantIndex i)
            (K * ((8 * m + 5) ^ d)) ∩
          (seedConnectionEvent d i m n)ᶜ) ≤
      (bernoulliBondMeasure d p).real
          (orthantBoundaryContactCardGeEvent d m n
            (allPositiveBoxSurfaceOrthantIndex i)
            (K * ((8 * m + 5) ^ d))) *
        (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ K := by
  classical
  let a := allPositiveBoxSurfaceOrthantIndex i
  let ell := K * ((8 * m + 5) ^ d)
  let C := largeOrthantBoundaryContactSets d n a ell
  let history : Finset (Cubic d) → Set (EdgeConfiguration d) := fun S =>
    orthantBoundaryContactSetEvent d m n a S
  let bad : Finset (Cubic d) → Set (EdgeConfiguration d) := fun S =>
    history S ∩ (seedConnectionEvent d i m n)ᶜ
  have hge : orthantBoundaryContactCardGeEvent d m n a ell =
      ⋃ S ∈ C, history S := by
    exact orthantBoundaryContactCardGeEvent_eq_biUnion_contactSet d m n a ell
  have hbadEq :
      orthantBoundaryContactCardGeEvent d m n a ell ∩
          (seedConnectionEvent d i m n)ᶜ = ⋃ S ∈ C, bad S := by
    rw [hge]
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion, bad, history]
    constructor
    · rintro ⟨⟨S, hSC, hHistory⟩, hNot⟩
      exact ⟨S, hSC, hHistory, hNot⟩
    · rintro ⟨S, hSC, hHistory, hNot⟩
      exact ⟨⟨S, hSC, hHistory⟩, hNot⟩
  have hpairHistory : Set.PairwiseDisjoint (C : Set (Finset (Cubic d))) history := by
    exact pairwiseDisjoint_orthantBoundaryContactSetEvent d m n a ell
  have hpairBad : Set.PairwiseDisjoint (C : Set (Finset (Cubic d))) bad :=
    hpairHistory.mono fun _S => Set.inter_subset_left
  have hgeSum :
      (bernoulliBondMeasure d p).real
          (orthantBoundaryContactCardGeEvent d m n a ell) =
        ∑ S ∈ C, (bernoulliBondMeasure d p).real (history S) := by
    rw [hge]
    exact measureReal_biUnion_finset hpairHistory
      (fun S _hS => measurableSet_orthantBoundaryContactSetEvent d m n a S)
  have hbadSum :
      (bernoulliBondMeasure d p).real
          (orthantBoundaryContactCardGeEvent d m n a ell ∩
            (seedConnectionEvent d i m n)ᶜ) =
        ∑ S ∈ C, (bernoulliBondMeasure d p).real (bad S) := by
    rw [hbadEq]
    exact measureReal_biUnion_finset hpairBad fun S _hS =>
      (measurableSet_orthantBoundaryContactSetEvent d m n a S).inter
        (measurableSet_seedConnectionEvent d i m n).compl
  have hterm : ∀ S ∈ C,
      (bernoulliBondMeasure d p).real (bad S) ≤
        (bernoulliBondMeasure d p).real (history S) *
          (1 - (p : ℝ) ^ (1 + (2 * m + 1) ^ d * (2 * d))) ^ K := by
    intro S hSC
    have hS := mem_largeOrthantBoundaryContactSets_iff.mp hSC
    exact orthantContactSet_inter_seedConnection_compl_probability_le
      p i S hmn hS.1 (by simpa [ell] using hS.2)
  rw [hbadSum, hgeSum, Finset.sum_mul]
  exact Finset.sum_le_sum fun S hS => hterm S hS

/-- The inner radius can be chosen before the requested contact cardinality.  This removes the
only apparent circularity in seed amplification, since the packing factor depends on `m`. -/
theorem exists_uniformInnerRadius_forall_eventually_allPositiveOrthantContactCardGe_probability_gt
    (d : ℕ) [NeZero d] (hd : 0 < d) (p : I) (htheta : 0 < theta d p)
    (hp1 : (p : ℝ) < 1) (i : Fin d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, ∀ ell : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      m ≤ n ∧
        1 - epsilon <
          (bernoulliBondMeasure d p).real
            (orthantBoundaryContactCardGeEvent d m n
              (allPositiveBoxSurfaceOrthantIndex i) ell) := by
  let Q : ℕ := d * 2 ^ d
  have hQ : Q ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt hd) (pow_ne_zero _ (by omega))
  have hepsilonPow : 0 < epsilon ^ Q := pow_pos hepsilon Q
  obtain ⟨m, hm⟩ := exists_centralBoxMeetsInfiniteCluster_probability_gt
    d p htheta (half_pos hepsilonPow)
  refine ⟨m, ?_⟩
  intro ell
  have hsmallT := smallNonemptyBoundaryContact_probability_tendsto_zero
    d m (Q * ell) p hp1
  have hsmallEventually : ∀ᶠ n : ℕ in Filter.atTop,
      (bernoulliBondMeasure d p).real
          (smallNonemptyBoundaryContactEvent d m n (Q * ell)) < epsilon ^ Q / 2 :=
    hsmallT.eventually (Iio_mem_nhds (half_pos hepsilonPow))
  have hmnEventually : ∀ᶠ n : ℕ in Filter.atTop, m ≤ n :=
    Filter.Ici_mem_atTop m
  filter_upwards [hmnEventually, hsmallEventually] with n hmn hsmall
  let mu := bernoulliBondMeasure d p
  have hempty := emptyBoundaryContact_probability_le_one_sub_central d p hmn
  have hbadUnion := boundaryContactCardLt_probability_le_empty_add_small
    d m n (Q * ell) p
  have hfullBad :
      mu.real (boundaryContactCardLtEvent d m n (Q * ell)) < epsilon ^ Q := by
    dsimp [mu]
    linarith
  have hpow := orthantContactLt_probability_pow_le_fullContactLt
    (d := d) (m := m) (n := n) (ell := ell) hd p i
  have hrefPow :
      (mu.real (orthantBoundaryContactCardLtEvent d m n
        (allPositiveBoxSurfaceOrthantIndex i) ell)) ^ Q < epsilon ^ Q :=
    hpow.trans_lt (by simpa [Q, mu] using hfullBad)
  have hrefBad :
      mu.real (orthantBoundaryContactCardLtEvent d m n
        (allPositiveBoxSurfaceOrthantIndex i) ell) < epsilon :=
    (pow_lt_pow_iff_left₀ measureReal_nonneg (le_of_lt hepsilon) hQ).mp hrefPow
  have hrefCompl :
      mu.real (orthantBoundaryContactCardLtEvent d m n
          (allPositiveBoxSurfaceOrthantIndex i) ell) +
        mu.real (orthantBoundaryContactCardGeEvent d m n
          (allPositiveBoxSurfaceOrthantIndex i) ell) = 1 := by
    have h := probReal_add_probReal_compl
      (μ := mu) (measurableSet_orthantBoundaryContactCardLtEvent d m n
        (allPositiveBoxSurfaceOrthantIndex i) ell)
    rwa [← orthantBoundaryContactCardGeEvent_eq_compl] at h
  exact ⟨hmn, by linarith⟩

/-- Grimmett Lemma 7.9: in the percolating regime at a nontrivial density, a central box connects
inside a larger box to a fully open seed on the selected boundary quadrant with arbitrarily high
probability. -/
theorem seedConnection_probability_gt
    (d : ℕ) [NeZero d] (hd : 0 < d) (p : I)
    (htheta : 0 < theta d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m n : ℕ, 2 * m < n ∧
      1 - epsilon <
        (bernoulliBondMeasure d p).real (seedConnectionEvent d i m n) := by
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := half_pos hepsilon
  obtain ⟨m, hmContacts⟩ :=
    exists_uniformInnerRadius_forall_eventually_allPositiveOrthantContactCardGe_probability_gt
      d hd p htheta hp1 i hdelta
  let M : ℕ := 1 + (2 * m + 1) ^ d * (2 * d)
  let q : ℝ := (p : ℝ) ^ M
  have hqPos : 0 < q := pow_pos hp0 M
  have hqLeOne : q ≤ 1 := by
    exact pow_le_one₀ p.2.1 p.2.2
  let r : ℝ := 1 - q
  have hrNonneg : 0 ≤ r := sub_nonneg.mpr hqLeOne
  have hrLtOne : r < 1 := by dsimp [r]; linarith
  have hrTendsto : Filter.Tendsto (fun K : ℕ => r ^ K)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrNonneg hrLtOne
  have hrEventually : ∀ᶠ K : ℕ in Filter.atTop, r ^ K < delta :=
    hrTendsto.eventually (Iio_mem_nhds hdelta)
  obtain ⟨K, hK⟩ := hrEventually.exists
  let ell : ℕ := K * ((8 * m + 5) ^ d)
  have hcontactEventually := hmContacts ell
  have hlargeEventually : ∀ᶠ n : ℕ in Filter.atTop, 2 * m < n := by
    filter_upwards [Filter.Ici_mem_atTop (2 * m + 1)] with n hn
    omega
  obtain ⟨n, hnContact, hmn⟩ := (hcontactEventually.and hlargeEventually).exists
  have hmnLe : 2 * m ≤ n := hmn.le
  let A := orthantBoundaryContactCardGeEvent d m n
    (allPositiveBoxSurfaceOrthantIndex i) ell
  let mu := bernoulliBondMeasure d p
  have hAhigh : 1 - delta < mu.real A := by
    simpa [A] using hnContact.2
  have hAcompl : mu.real Aᶜ < delta := by
    rw [probReal_compl_eq_one_sub
      (measurableSet_orthantBoundaryContactCardGeEvent d m n
        (allPositiveBoxSurfaceOrthantIndex i) ell)]
    linarith
  have hamp : mu.real (A ∩ (seedConnectionEvent d i m n)ᶜ) ≤
      mu.real A * r ^ K := by
    simpa [A, mu, ell, r, q, M] using
      orthantContactGe_inter_seedConnection_compl_probability_le p i hmnLe (K := K)
  have hAmpLt : mu.real (A ∩ (seedConnectionEvent d i m n)ᶜ) < delta := by
    calc
      mu.real (A ∩ (seedConnectionEvent d i m n)ᶜ) ≤ mu.real A * r ^ K := hamp
      _ ≤ 1 * r ^ K := by
        exact mul_le_mul_of_nonneg_right (measureReal_le_one) (pow_nonneg hrNonneg K)
      _ < delta := by simpa using hK
  have hseedComplSubset : (seedConnectionEvent d i m n)ᶜ ⊆
      Aᶜ ∪ (A ∩ (seedConnectionEvent d i m n)ᶜ) := by
    intro omega hseed
    by_cases hA : omega ∈ A
    · exact Or.inr ⟨hA, hseed⟩
    · exact Or.inl hA
  have hseedCompl : mu.real (seedConnectionEvent d i m n)ᶜ < epsilon := by
    calc
      mu.real (seedConnectionEvent d i m n)ᶜ ≤
          mu.real (Aᶜ ∪ (A ∩ (seedConnectionEvent d i m n)ᶜ)) :=
        measureReal_mono hseedComplSubset (measure_ne_top _ _)
      _ ≤ mu.real Aᶜ + mu.real (A ∩ (seedConnectionEvent d i m n)ᶜ) :=
        measureReal_union_le _ _
      _ < epsilon := by dsimp [delta] at hAcompl hAmpLt ⊢; linarith
  have hcomplSum :
      mu.real (seedConnectionEvent d i m n) +
        mu.real (seedConnectionEvent d i m n)ᶜ = 1 :=
    probReal_add_probReal_compl (measurableSet_seedConnectionEvent d i m n)
  exact ⟨m, n, hmn, by linarith⟩

end Percolation
