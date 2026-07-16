import Percolation.Bernoulli.FiniteEventContinuity
import Percolation.Critical.FiniteCylinderTranslation
import Percolation.Critical.StaticBlocks

/-!
# Seeds and seeded boundary connection events

These are the finite geometric events in Grimmett (7.5)--(7.10).  A seed is a translated box
whose internal bonds are all open.  The target set retains the source's existential choice of a
seed containing the outward neighbor, rather than fixing an artificial seed center.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Every internal edge of `x + B(m)` is open. -/
def cubicSeedEvent (d : ℕ) (x : Cubic d) (m : ℕ) : Set (EdgeConfiguration d) :=
  openEdgeSetEvent d (cubicBoxEdges d x m)

theorem measurableSet_cubicSeedEvent (d : ℕ) (x : Cubic d) (m : ℕ) :
    MeasurableSet (cubicSeedEvent d x m) :=
  measurableSet_openEdgeSetEvent d (cubicBoxEdges d x m)

theorem isIncreasingEvent_cubicSeedEvent (d : ℕ) (x : Cubic d) (m : ℕ) :
    IsIncreasingEvent (cubicSeedEvent d x m) := by
  intro ω η hωη hω e he
  exact hωη (hω he)

theorem bernoulliBondMeasure_real_cubicSeedEvent (d : ℕ) (p : I)
    (x : Cubic d) (m : ℕ) :
    (bernoulliBondMeasure d p).real (cubicSeedEvent d x m) =
      (p : ℝ) ^ (cubicBoxEdges d x m).card := by
  exact bernoulliBondMeasure_real_openEdgeSetEvent d p (cubicBoxEdges d x m)

/-- The positive quadrant of a selected positive box face, corresponding to `T(n)` in (7.6). -/
noncomputable def seededBoundaryQuadrant
    (d : ℕ) (i : Fin d) (n : ℕ) : Finset (Cubic d) :=
  (cubicBoxFace d cubicOrigin n i true).filter fun x ↦
    ∀ j : Fin d, j ≠ i → 0 ≤ x j

@[simp]
theorem mem_seededBoundaryQuadrant_iff {d n : ℕ} {i : Fin d} {x : Cubic d} :
    x ∈ seededBoundaryQuadrant d i n ↔
      x ∈ cubicBoxFace d cubicOrigin n i true ∧ ∀ j, j ≠ i → 0 ≤ x j := by
  classical
  simp [seededBoundaryQuadrant]

/-- Translation of a vertex by `r` positive steps in coordinate `i`. -/
def cubicTranslateAlongCoordinate {d : ℕ} (x : Cubic d) (i : Fin d) (r : ℕ) : Cubic d :=
  Function.update x i (x i + r)

@[simp]
theorem cubicTranslateAlongCoordinate_same {d : ℕ}
    (x : Cubic d) (i : Fin d) (r : ℕ) :
    cubicTranslateAlongCoordinate x i r i = x i + r := by
  simp [cubicTranslateAlongCoordinate]

theorem cubicTranslateAlongCoordinate_of_ne {d : ℕ}
    (x : Cubic d) {i j : Fin d} (hji : j ≠ i) (r : ℕ) :
    cubicTranslateAlongCoordinate x i r j = x j := by
  simp [cubicTranslateAlongCoordinate, hji]

/-- The layered region `T(m,n)` from (7.7). -/
def seededBoundaryLayerRegion (d : ℕ) (i : Fin d) (m n : ℕ) : Set (Cubic d) :=
  {z | ∃ r : ℕ, 1 ≤ r ∧ r ≤ 2 * m + 1 ∧
    ∃ y ∈ seededBoundaryQuadrant d i n, z = cubicTranslateAlongCoordinate y i r}

/-- The entire layered target lies in the radius `n + 2m + 1` coordinate box. -/
theorem seededBoundaryLayerRegion_mem_wideBox
    {d m n : ℕ} {i : Fin d} {z : Cubic d}
    (hz : z ∈ seededBoundaryLayerRegion d i m n) :
    z ∈ cubicMetricBox d cubicOrigin (n + 2 * m + 1) := by
  rcases hz with ⟨r, _hr1, hrUpper, y, hyQuadrant, rfl⟩
  rw [mem_cubicMetricBox]
  intro j
  have hyFace := mem_cubicBoxFace.mp
    (mem_seededBoundaryQuadrant_iff.mp hyQuadrant).1
  by_cases hji : j = i
  · subst j
    have hyi : y i = (n : ℤ) := by
      simpa [cubicOrigin] using hyFace.1
    rw [cubicTranslateAlongCoordinate_same, hyi]
    simp [cubicOrigin]
    constructor <;> omega
  · rw [cubicTranslateAlongCoordinate_of_ne y hji]
    have hjBounds := hyFace.2 j hji
    have hjLower : -(n : ℤ) ≤ y j := by
      simpa [cubicOrigin] using hjBounds.1
    have hjUpper : y j ≤ (n : ℤ) := by
      simpa [cubicOrigin] using hjBounds.2
    simp [cubicOrigin]
    constructor <;> omega

/-- A translated seed box lies wholly in the layered boundary region. -/
def SeedBoxWithinBoundaryLayer
    (d : ℕ) (i : Fin d) (m n : ℕ) (c : Cubic d) : Prop :=
  ∀ z ∈ cubicMetricBox d c m, z ∈ seededBoundaryLayerRegion d i m n

/-- A boundary vertex belongs to the random target set `K(m,n)` of (7.8). -/
def IsSeededBoundaryPoint (d : ℕ) (i : Fin d) (m n : ℕ)
    (ω : EdgeConfiguration d) (y : Cubic d) : Prop :=
  y ∈ seededBoundaryQuadrant d i n ∧
    cubicStepEdge y (i, true) ∈ ω ∧
    ∃ c : Cubic d,
      cubicStepFrom y (i, true) ∈ cubicMetricBox d c m ∧
      SeedBoxWithinBoundaryLayer d i m n c ∧
      ω ∈ cubicSeedEvent d c m

/-- The random set `K(m,n)`. -/
def seededBoundaryPoints (d : ℕ) (i : Fin d) (m n : ℕ)
    (ω : EdgeConfiguration d) : Set (Cubic d) :=
  {y | IsSeededBoundaryPoint d i m n ω y}

/-- The target set `K(m,n)` is empty when the boundary face is too narrow to contain a
codimension-one seed.  The dimension hypothesis is necessary: in dimension one there is no
transverse coordinate that forces the width bound. -/
theorem seededBoundaryPoints_eq_empty_of_lt_two_mul {d m n : ℕ} (hd : 2 ≤ d)
    (i : Fin d) (ω : EdgeConfiguration d) (hn : n < 2 * m) :
    seededBoundaryPoints d i m n ω = ∅ := by
  classical
  ext y
  simp only [seededBoundaryPoints, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hyQ, _hyedge, c, _hyc, hcLayer, _hcSeed⟩
  let j : Fin d := if hi : i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hji : j ≠ i := by
    by_cases hi : i.val = 0
    · intro h
      have hval := congrArg Fin.val h
      simp [j, hi] at hval
    · intro h
      have hval := congrArg Fin.val h
      simp [j, hi] at hval
      exact hi hval.symm
  let zminus : Cubic d := Function.update c j (c j - (m : ℤ))
  let zplus : Cubic d := Function.update c j (c j + (m : ℤ))
  have hzminus : zminus ∈ cubicMetricBox d c m := by
    rw [mem_cubicMetricBox]
    intro k
    by_cases hkj : k = j
    · subst k
      simp [zminus]
      omega
    · simpa [zminus, hkj]
  have hzplus : zplus ∈ cubicMetricBox d c m := by
    rw [mem_cubicMetricBox]
    intro k
    by_cases hkj : k = j
    · subst k
      simp [zplus]
      omega
    · simpa [zplus, hkj]
  obtain ⟨rminus, _hrminus1, _hrminus2, yminus, hyminusQ, hzminusEq⟩ :=
    hcLayer zminus hzminus
  obtain ⟨rplus, _hrplus1, _hrplus2, yplus, hyplusQ, hzplusEq⟩ :=
    hcLayer zplus hzplus
  have hzminusj : c j - (m : ℤ) = yminus j := by
    have h := congrFun hzminusEq j
    rw [cubicTranslateAlongCoordinate_of_ne yminus hji rminus] at h
    simpa [zminus] using h
  have hzplusj : c j + (m : ℤ) = yplus j := by
    have h := congrFun hzplusEq j
    rw [cubicTranslateAlongCoordinate_of_ne yplus hji rplus] at h
    simpa [zplus] using h
  have hyminus_nonneg : 0 ≤ yminus j :=
    (mem_seededBoundaryQuadrant_iff.mp hyminusQ).2 j hji
  have hyplus_le : yplus j ≤ (n : ℤ) := by
    have hface := mem_cubicBoxFace.mp (mem_seededBoundaryQuadrant_iff.mp hyplusQ).1
    have hj := (hface.2 j hji).2
    simpa [cubicOrigin] using hj
  omega

/-- A finite ambient set containing every seed center that can witness membership in `K(m,n)`. -/
noncomputable def seededBoundaryPossibleCenters
    (d : ℕ) (m n : ℕ) : Finset (Cubic d) :=
  cubicMetricBox d cubicOrigin (n + m + 1)

theorem seedCenter_mem_seededBoundaryPossibleCenters
    {d m n : ℕ} {i : Fin d} {y c : Cubic d}
    (hy : y ∈ seededBoundaryQuadrant d i n)
    (hyc : cubicStepFrom y (i, true) ∈ cubicMetricBox d c m) :
    c ∈ seededBoundaryPossibleCenters d m n := by
  have hyface := (mem_seededBoundaryQuadrant_iff.mp hy).1
  have hybox : y ∈ cubicMetricBox d cubicOrigin n := by
    rw [mem_cubicMetricBox]
    intro j
    have hface := mem_cubicBoxFace.mp hyface
    by_cases hji : j = i
    · subst j
      simp [cubicOrigin] at hface ⊢
      omega
    · have hj := hface.2 j hji
      simp [cubicOrigin] at hj ⊢
      omega
  apply mem_cubicMetricBox_iff_lInfDist_le.mpr
  calc
    cubicLInfDist cubicOrigin c ≤
        cubicLInfDist cubicOrigin y +
          cubicLInfDist y (cubicStepFrom y (i, true)) +
            cubicLInfDist (cubicStepFrom y (i, true)) c := by
      have h₁ := cubicLInfDist_triangle cubicOrigin y c
      have h₂ := cubicLInfDist_triangle y (cubicStepFrom y (i, true)) c
      omega
    _ ≤ n + 1 + m := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (mem_cubicMetricBox_iff_lInfDist_le.mp hybox)
          (cubicLInfDist_stepFrom_le_one y (i, true)))
        (by rw [cubicLInfDist_comm]; exact mem_cubicMetricBox_iff_lInfDist_le.mp hyc)
    _ = n + m + 1 := by omega

/-- Exact finite set of seed centers that can occur in the prescribed layered target region.
The older ambient box remains useful as a finite enumeration type, but using that coarse box
as an edge dependency set would include impossible seed boxes on the wrong side of the face. -/
noncomputable def seededBoundaryAdmissibleCenters
    (d : ℕ) (i : Fin d) (m n : ℕ) : Finset (Cubic d) := by
  classical
  exact (seededBoundaryPossibleCenters d m n).filter
    (SeedBoxWithinBoundaryLayer d i m n)

@[simp]
theorem mem_seededBoundaryAdmissibleCenters_iff
    {d m n : ℕ} {i : Fin d} {c : Cubic d} :
    c ∈ seededBoundaryAdmissibleCenters d i m n ↔
      c ∈ seededBoundaryPossibleCenters d m n ∧
        SeedBoxWithinBoundaryLayer d i m n c := by
  classical
  simp [seededBoundaryAdmissibleCenters]

theorem seedCenter_mem_seededBoundaryAdmissibleCenters
    {d m n : ℕ} {i : Fin d} {y c : Cubic d}
    (hy : y ∈ seededBoundaryQuadrant d i n)
    (hyc : cubicStepFrom y (i, true) ∈ cubicMetricBox d c m)
    (hcLayer : SeedBoxWithinBoundaryLayer d i m n c) :
    c ∈ seededBoundaryAdmissibleCenters d i m n :=
  mem_seededBoundaryAdmissibleCenters_iff.mpr
    ⟨seedCenter_mem_seededBoundaryPossibleCenters hy hyc, hcLayer⟩

/-- Finite edge support deciding the seeded connection event. -/
noncomputable def seedConnectionSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) : Finset (CubicEdge d) := by
  classical
  exact cubicBoxEdges d cubicOrigin n ∪
    (seededBoundaryQuadrant d i n).image (fun y ↦ cubicStepEdge y (i, true)) ∪
      (seededBoundaryAdmissibleCenters d i m n).biUnion fun c ↦
        cubicBoxEdges d c m

/-- The exact seeded-connection dependency set fits in the smallest obvious wide box. -/
theorem seedConnectionSupport_subset_cubicBoxEdges_wide
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    seedConnectionSupport d i m n ⊆
      cubicBoxEdges d cubicOrigin (n + 2 * m + 1) := by
  classical
  intro e he
  rw [seedConnectionSupport] at he
  simp only [Finset.mem_union] at he
  apply mem_cubicBoxEdges_of_endpoints
  intro z hze
  rcases he with (heBox | heStep) | heSeed
  · apply mem_cubicMetricBox_iff_lInfDist_le.mpr
    exact (mem_cubicMetricBox_iff_lInfDist_le.mp
      (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hze)).trans
        (by omega)
  · obtain ⟨y, hyQuadrant, rfl⟩ := Finset.mem_image.mp heStep
    change z ∈ s(y, cubicStepFrom y (i, true)) at hze
    rw [Sym2.mem_iff] at hze
    have hyFace := mem_cubicBoxFace.mp
      (mem_seededBoundaryQuadrant_iff.mp hyQuadrant).1
    have hyWide : y ∈ cubicMetricBox d cubicOrigin (n + 2 * m + 1) := by
      rw [mem_cubicMetricBox]
      intro j
      by_cases hji : j = i
      · subst j
        have hyi : y i = (n : ℤ) := by
          simpa [cubicOrigin] using hyFace.1
        simp [hyi, cubicOrigin]
        constructor <;> omega
      · have hjBounds := hyFace.2 j hji
        have hjLower : -(n : ℤ) ≤ y j := by
          simpa [cubicOrigin] using hjBounds.1
        have hjUpper : y j ≤ (n : ℤ) := by
          simpa [cubicOrigin] using hjBounds.2
        simp [cubicOrigin]
        constructor <;> omega
    have hstepWide : cubicStepFrom y (i, true) ∈
        cubicMetricBox d cubicOrigin (n + 2 * m + 1) := by
      rw [mem_cubicMetricBox]
      intro j
      by_cases hji : j = i
      · subst j
        have hyi : y i = (n : ℤ) := by
          simpa [cubicOrigin] using hyFace.1
        have hstepi : cubicStepFrom y (i, true) i = (n : ℤ) + 1 := by
          simp [cubicStepFrom, cubicDirectionIncrement, hyi]
        rw [hstepi]
        simp [cubicOrigin]
        omega
      · have hjBounds := hyFace.2 j hji
        have hjLower : -(n : ℤ) ≤ y j := by
          simpa [cubicOrigin] using hjBounds.1
        have hjUpper : y j ≤ (n : ℤ) := by
          simpa [cubicOrigin] using hjBounds.2
        have hstepj : cubicStepFrom y (i, true) j = y j := by
          simp [cubicStepFrom, cubicDirectionIncrement, hji]
        rw [hstepj]
        simp [cubicOrigin]
        constructor <;> omega
    rcases hze with hzy | hzstep
    · subst z
      exact hyWide
    · subst z
      exact hstepWide
  · rw [Finset.mem_biUnion] at heSeed
    obtain ⟨c, hcAdmissible, heSeed⟩ := heSeed
    exact seededBoundaryLayerRegion_mem_wideBox
      ((mem_seededBoundaryAdmissibleCenters_iff.mp hcAdmissible).2 z
        (endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heSeed hze))

/-- For a fixed boundary vertex, being a seeded target is measurable.  The possible seed
centers form a countable (not definitionally finite) union; retaining that union is important
because `IsSeededBoundaryPoint` deliberately uses Grimmett's existential choice of seed. -/
theorem measurableSet_isSeededBoundaryPoint
    (d : ℕ) (i : Fin d) (m n : ℕ) (y : Cubic d) :
    MeasurableSet {ω : EdgeConfiguration d | IsSeededBoundaryPoint d i m n ω y} := by
  classical
  by_cases hy : y ∈ seededBoundaryQuadrant d i n
  · have hc : MeasurableSet
        (⋃ c : Cubic d,
          if cubicStepFrom y (i, true) ∈ cubicMetricBox d c m ∧
              SeedBoxWithinBoundaryLayer d i m n c then
            cubicSeedEvent d c m
          else ∅) := by
      apply MeasurableSet.iUnion
      intro c
      split_ifs
      · exact measurableSet_cubicSeedEvent d c m
      · exact MeasurableSet.empty
    have he : MeasurableSet
        {ω : EdgeConfiguration d | cubicStepEdge y (i, true) ∈ ω} :=
      measurableSet_mem _
    have hset : {ω : EdgeConfiguration d | IsSeededBoundaryPoint d i m n ω y} =
        {ω : EdgeConfiguration d | cubicStepEdge y (i, true) ∈ ω} ∩
          ⋃ c : Cubic d,
            if cubicStepFrom y (i, true) ∈ cubicMetricBox d c m ∧
                SeedBoxWithinBoundaryLayer d i m n c then
              cubicSeedEvent d c m
            else ∅ := by
      ext ω
      change IsSeededBoundaryPoint d i m n ω y ↔
        cubicStepEdge y (i, true) ∈ ω ∧
          ω ∈ ⋃ c : Cubic d,
            if cubicStepFrom y (i, true) ∈ cubicMetricBox d c m ∧
                SeedBoxWithinBoundaryLayer d i m n c then
              cubicSeedEvent d c m
            else ∅
      constructor
      · rintro ⟨_hy, hyedge, c, hyc, hcLayer, hcSeed⟩
        refine ⟨hyedge, Set.mem_iUnion.mpr ⟨c, ?_⟩⟩
        rw [if_pos ⟨hyc, hcLayer⟩]
        exact hcSeed
      · rintro ⟨hyedge, hc⟩
        obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hc
        by_cases hgeom : cubicStepFrom y (i, true) ∈ cubicMetricBox d c m ∧
            SeedBoxWithinBoundaryLayer d i m n c
        · rw [if_pos hgeom] at hc
          exact ⟨hy, hyedge, c, hgeom.1, hgeom.2, hc⟩
        · rw [if_neg hgeom] at hc
          exact hc.elim
    rw [hset]
    exact he.inter hc
  · have : {ω : EdgeConfiguration d | IsSeededBoundaryPoint d i m n ω y} = ∅ := by
      ext ω
      simp [IsSeededBoundaryPoint, hy]
    rw [this]
    exact MeasurableSet.empty

/-- The event in (7.10): some vertex of `B(m)` is connected inside `B(n)` to `K(m,n)`. -/
def seedConnectionEvent (d : ℕ) (i : Fin d) (m n : ℕ) :
    Set (EdgeConfiguration d) :=
  {ω | ∃ x ∈ cubicMetricBox d cubicOrigin m,
    ∃ y ∈ seededBoundaryPoints d i m n ω,
      ω ∈ connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y}

theorem measurableSet_seedConnectionEvent (d : ℕ) (i : Fin d) (m n : ℕ) :
    MeasurableSet (seedConnectionEvent d i m n) := by
  have hxy : ∀ x y : Cubic d, MeasurableSet
      ({ω : EdgeConfiguration d | IsSeededBoundaryPoint d i m n ω y} ∩
        connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y) := by
    intro x y
    exact (measurableSet_isSeededBoundaryPoint d i m n y).inter
      (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y).measurableSet
  have hUnion : MeasurableSet
      (⋃ x ∈ cubicMetricBox d cubicOrigin m,
        ⋃ y : Cubic d,
          {ω : EdgeConfiguration d | IsSeededBoundaryPoint d i m n ω y} ∩
            connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y) := by
    apply (cubicMetricBox d cubicOrigin m).measurableSet_biUnion
    intro x _hx
    exact MeasurableSet.iUnion fun y ↦ hxy x y
  convert hUnion using 1
  ext ω
  simp only [seedConnectionEvent, seededBoundaryPoints, Set.mem_setOf_eq, Set.mem_iUnion,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy, hxy⟩

theorem dependsOn_seedConnectionEvent (d : ℕ) (i : Fin d) (m n : ℕ) :
    DependsOn (seedConnectionSupport d i m n) (seedConnectionEvent d i m n) := by
  classical
  intro ω η hagree
  have hagreeConnection : ∀ e ∈ cubicBoxEdges d cubicOrigin n, (e ∈ ω ↔ e ∈ η) := by
    intro e he
    apply hagree e
    rw [seedConnectionSupport]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  constructor
  · rintro ⟨x, hx, y, ⟨hyQ, hyedge, c, hyc, hcLayer, hcSeed⟩, hxy⟩
    have hedgeSupport : cubicStepEdge y (i, true) ∈ seedConnectionSupport d i m n := by
      rw [seedConnectionSupport]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨y, hyQ, rfl⟩
    have hcCenter : c ∈ seededBoundaryAdmissibleCenters d i m n :=
      seedCenter_mem_seededBoundaryAdmissibleCenters hyQ hyc hcLayer
    have hcSeed' : η ∈ cubicSeedEvent d c m := by
      intro e he
      apply (hagree e ?_).mp (hcSeed he)
      rw [seedConnectionSupport]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨c, hcCenter, he⟩
    exact ⟨x, hx, y,
      ⟨hyQ, (hagree _ hedgeSupport).mp hyedge, c, hyc, hcLayer, hcSeed'⟩,
      (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y
        hagreeConnection).mp hxy⟩
  · rintro ⟨x, hx, y, ⟨hyQ, hyedge, c, hyc, hcLayer, hcSeed⟩, hxy⟩
    have hedgeSupport : cubicStepEdge y (i, true) ∈ seedConnectionSupport d i m n := by
      rw [seedConnectionSupport]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨y, hyQ, rfl⟩
    have hcCenter : c ∈ seededBoundaryAdmissibleCenters d i m n :=
      seedCenter_mem_seededBoundaryAdmissibleCenters hyQ hyc hcLayer
    have hcSeed' : ω ∈ cubicSeedEvent d c m := by
      intro e he
      apply (hagree e ?_).mpr (hcSeed he)
      rw [seedConnectionSupport]
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨c, hcCenter, he⟩
    exact ⟨x, hx, y,
      ⟨hyQ, (hagree _ hedgeSupport).mpr hyedge, c, hyc, hcLayer, hcSeed'⟩,
      (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y
        hagreeConnection).mpr hxy⟩

theorem continuous_seedConnectionProbability
    (d : ℕ) (i : Fin d) (m n : ℕ) :
    Continuous fun x : ℝ ↦
      (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one x)).real
        (seedConnectionEvent d i m n) :=
  (dependsOn_seedConnectionEvent d i m n).continuous_bernoulliBondMeasure_real

theorem isIncreasingEvent_seedConnectionEvent (d : ℕ) (i : Fin d) (m n : ℕ) :
    IsIncreasingEvent (seedConnectionEvent d i m n) := by
  rintro ω η hωη ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, y, ?_,
    isIncreasingEvent_connectionEventIn d (cubicBoxEdges d cubicOrigin n) x y hωη hxy⟩
  rcases hy with ⟨hyQ, hyedge, c, hyc, hcLayer, hcSeed⟩
  exact ⟨hyQ, hωη hyedge, c, hyc, hcLayer,
    isIncreasingEvent_cubicSeedEvent d c m hωη hcSeed⟩

end Percolation
