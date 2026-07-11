import Percolation.Bernoulli.FiniteEventContinuity
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

/-- Finite edge support deciding the seeded connection event. -/
noncomputable def seedConnectionSupport
    (d : ℕ) (i : Fin d) (m n : ℕ) : Finset (CubicEdge d) := by
  classical
  exact cubicBoxEdges d cubicOrigin n ∪
    (seededBoundaryQuadrant d i n).image (fun y ↦ cubicStepEdge y (i, true)) ∪
      (seededBoundaryPossibleCenters d m n).biUnion fun c ↦ cubicBoxEdges d c m

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
    have hcCenter : c ∈ seededBoundaryPossibleCenters d m n :=
      seedCenter_mem_seededBoundaryPossibleCenters hyQ hyc
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
    have hcCenter : c ∈ seededBoundaryPossibleCenters d m n :=
      seedCenter_mem_seededBoundaryPossibleCenters hyQ hyc
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
