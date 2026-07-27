import Percolation.Critical.StaticBlockSliceCrossing
import Percolation.Critical.StaticLargeCrossing
import Percolation.Core.EdgeMengerToSet
import Percolation.Planar.CrossingMenger

/-!
# Static renormalization: macroscopic box crossings

This file assembles the translated planar good-block slices from equations (7.72)--(7.74) into
literal left-right crossings of the ambient cubic box.  It then supplies the finite-box Menger
interface needed for the sprinkling step (7.75).
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Open crossings of the coordinate box from its negative to its positive face in coordinate
`i`. -/
def cubicBoxCrossingEvent (d r : ℕ) (i : Fin d) : Set (EdgeConfiguration d) :=
  ⋃ x ∈ cubicBoxFace d cubicOrigin r i false,
    ⋃ y ∈ cubicBoxFace d cubicOrigin r i true,
      connectionEventIn d (cubicBoxEdges d cubicOrigin r) x y

theorem measurableSet_cubicBoxCrossingEvent (d r : ℕ) (i : Fin d) :
    MeasurableSet (cubicBoxCrossingEvent d r i) := by
  apply (cubicBoxFace d cubicOrigin r i false).measurableSet_biUnion
  intro x _hx
  apply (cubicBoxFace d cubicOrigin r i true).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn d (cubicBoxEdges d cubicOrigin r) x y).measurableSet

theorem isIncreasingEvent_cubicBoxCrossingEvent (d r : ℕ) (i : Fin d) :
    IsIncreasingEvent (cubicBoxCrossingEvent d r i) := by
  intro ω η hωη hω
  simp only [cubicBoxCrossingEvent, Set.mem_iUnion] at hω ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := hω
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn d (cubicBoxEdges d cubicOrigin r) x y hωη hxy⟩

theorem staticSeparatedCoordinate_mem_bounds {K : ℕ} {a : ℤ}
    (ha : a ∈ staticSeparatedCoordinate K) :
    -(K : ℤ) ≤ a ∧ a ≤ (K : ℤ) := by
  rw [staticSeparatedCoordinate, Finset.mem_image] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  simp only [Finset.mem_Icc] at hu
  constructor <;> omega

theorem staticTransverseSliceIndices_coord_bounds
    {d K : ℕ} {k : Cubic (d - 2)}
    (hk : k ∈ staticTransverseSliceIndices d K) (i : Fin (d - 2)) :
    -(K : ℤ) ≤ k i ∧ k i ≤ (K : ℤ) := by
  exact staticSeparatedCoordinate_mem_bounds (Fintype.mem_piFinset.mp hk i)

/-- Every coarse vertex queried by a source-aligned translated slice lies in the coarse box
`B(K)`. -/
theorem cubicTranslatedFirstTwoEmbedding_staticTransverseSliceOffset_mem_box
    {d K : ℕ} (hd : 2 ≤ d) {k : Cubic (d - 2)}
    (hk : k ∈ staticTransverseSliceIndices d K)
    {x : SquareVertex} (hx : x ∈ squareRectangleVertices (2 * K) K) :
    cubicTranslatedFirstTwoEmbedding hd (staticTransverseSliceOffset d K k) x ∈
      cubicMetricBox d cubicOrigin K := by
  rw [mem_cubicMetricBox]
  intro j
  have hxData := mem_squareRectangleVertices_iff.mp hx
  by_cases hj0 : j.val = 0
  · have hj : j = (⟨0, by omega⟩ : Fin d) := Fin.ext hj0
    rw [hj]
    simp [cubicTranslatedFirstTwoEmbedding, cubicTranslate, cubicOrigin,
      staticTransverseSliceOffset, cubicEmbed]
    omega
  · by_cases hj1 : j.val = 1
    · have hj : j = (⟨1, hd⟩ : Fin d) := Fin.ext hj1
      rw [hj]
      simp [cubicTranslatedFirstTwoEmbedding, cubicTranslate, cubicOrigin,
        staticTransverseSliceOffset, cubicTransverseOffset, cubicEmbed]
      omega
    · have hj2 : 2 ≤ j.val := by omega
      let i : Fin (d - 2) := ⟨j.val - 2, by omega⟩
      have hkBounds := staticTransverseSliceIndices_coord_bounds hk i
      simpa [cubicTranslatedFirstTwoEmbedding, cubicTranslate, cubicOrigin,
        staticTransverseSliceOffset, cubicTransverseOffset, cubicEmbed,
        hj0, hj2, not_lt_of_ge hj2, i] using hkBounds

/-- A radius-`N` block centered at `N x`, for `x ∈ B(K)`, is contained in
`B(N(K+1))`. -/
theorem cubicMetricBox_epsilonGoodBlockCenter_subset_scaled_box
    {d N K : ℕ} {x : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin K) :
    (cubicMetricBox d (epsilonGoodBlockCenter N x) N : Set (Cubic d)) ⊆
      cubicMetricBox d cubicOrigin (N * (K + 1)) := by
  intro y hy
  change y ∈ cubicMetricBox d (epsilonGoodBlockCenter N x) N at hy
  change y ∈ cubicMetricBox d cubicOrigin (N * (K + 1))
  rw [mem_cubicMetricBox] at hx hy ⊢
  intro i
  have hxi := hx i
  have hyi := hy i
  have hN : (0 : ℤ) ≤ (N : ℤ) := by omega
  have hxLower := mul_le_mul_of_nonneg_left hxi.1 hN
  have hxUpper := mul_le_mul_of_nonneg_left hxi.2 hN
  simp only [cubicOrigin, zero_sub, zero_add,
    epsilonGoodBlockCenter, cubicScale] at hxi hyi ⊢
  norm_num [cubicOrigin, Nat.cast_mul, Nat.cast_add] at hxLower hxUpper ⊢
  constructor <;> nlinarith

theorem cubicBoxEdges_epsilonGoodBlockCenter_subset_scaled_box
    {d N K : ℕ} {x : Cubic d}
    (hx : x ∈ cubicMetricBox d cubicOrigin K) :
    cubicBoxEdges d (epsilonGoodBlockCenter N x) N ⊆
      cubicBoxEdges d cubicOrigin (N * (K + 1)) := by
  intro e he
  apply mem_cubicBoxEdges_of_endpoints
  intro y hy
  apply cubicMetricBox_epsilonGoodBlockCenter_subset_scaled_box hx
  exact endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges he hy

/-- All bond coordinates queried by a source-aligned transverse slice lie in the ambient
physical box `B(N(K+1))`. -/
theorem epsilonGoodBondTranslatedSliceCrossingSupport_static_subset_cubicBoxEdges
    {d N K : ℕ} (hd : 2 ≤ d) {k : Cubic (d - 2)}
    (hk : k ∈ staticTransverseSliceIndices d K) :
    epsilonGoodBondTranslatedSliceCrossingSupport d hd N
        (staticTransverseSliceOffset d K k) (2 * K) K ⊆
      cubicBoxEdges d cubicOrigin (N * (K + 1)) := by
  intro e he
  rw [epsilonGoodBondTranslatedSliceCrossingSupport, Finset.mem_biUnion] at he
  obtain ⟨x, hx, hex⟩ := he
  rw [epsilonGoodBlockTranslatedSliceCrossingSupport, Finset.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  apply cubicBoxEdges_epsilonGoodBlockCenter_subset_scaled_box
    (cubicTranslatedFirstTwoEmbedding_staticTransverseSliceOffset_mem_box hd hk hu)
  exact hex

theorem cubicBoxFace_subset_cubicMetricBox
    {d n : ℕ} {x y : Cubic d} {i : Fin d} {positive : Bool}
    (hy : y ∈ cubicBoxFace d x n i positive) :
    y ∈ cubicMetricBox d x n := by
  rw [mem_cubicBoxFace] at hy
  rw [mem_cubicMetricBox]
  intro j
  by_cases hji : j = i
  · subst j
    rcases positive with _ | _ <;> simp at hy ⊢ <;> omega
  · exact hy.2 j hji

theorem left_endpoint_staticTransverseSlice_mem_scaled_boxFace
    {d N K : ℕ} (hd : 2 ≤ d) {k : Cubic (d - 2)}
    (hk : k ∈ staticTransverseSliceIndices d K)
    {x : SquareVertex} (hx : x ∈ squareRectangleLeft (2 * K) K)
    {u : Cubic d}
    (hu : u ∈ cubicBoxFace d
      (epsilonGoodBlockCenter N
        (cubicTranslatedFirstTwoEmbedding hd (staticTransverseSliceOffset d K k) x))
      N (Fin.castLE hd 0) false) :
    u ∈ cubicBoxFace d cubicOrigin (N * (K + 1)) (Fin.castLE hd 0) false := by
  have hxRectangle : x ∈ squareRectangleVertices (2 * K) K :=
    by
      rw [squareRectangleLeft, Finset.mem_filter] at hx
      exact hx.1
  have hxCoarse :=
    cubicTranslatedFirstTwoEmbedding_staticTransverseSliceOffset_mem_box hd hk hxRectangle
  have huBox := cubicMetricBox_epsilonGoodBlockCenter_subset_scaled_box hxCoarse
    (cubicBoxFace_subset_cubicMetricBox hu)
  rw [mem_cubicBoxFace] at hu ⊢
  constructor
  · have hx0 := (mem_squareRectangleLeft_iff.mp hx).1
    have hcoord := hu.1
    simp [epsilonGoodBlockCenter, cubicScale, cubicTranslatedFirstTwoEmbedding,
      cubicTranslate, cubicOrigin, staticTransverseSliceOffset, cubicEmbed, hx0,
      Nat.cast_mul, Nat.cast_add] at hcoord ⊢
    nlinarith
  · intro j _hji
    exact (mem_cubicMetricBox.mp huBox j)

theorem right_endpoint_staticTransverseSlice_mem_scaled_boxFace
    {d N K : ℕ} (hd : 2 ≤ d) {k : Cubic (d - 2)}
    (hk : k ∈ staticTransverseSliceIndices d K)
    {y : SquareVertex} (hy : y ∈ squareRectangleRight (2 * K) K)
    {v : Cubic d}
    (hv : v ∈ cubicBoxFace d
      (epsilonGoodBlockCenter N
        (cubicTranslatedFirstTwoEmbedding hd (staticTransverseSliceOffset d K k) y))
      N (Fin.castLE hd 0) true) :
    v ∈ cubicBoxFace d cubicOrigin (N * (K + 1)) (Fin.castLE hd 0) true := by
  have hyRectangle : y ∈ squareRectangleVertices (2 * K) K :=
    by
      rw [squareRectangleRight, Finset.mem_filter] at hy
      exact hy.1
  have hyCoarse :=
    cubicTranslatedFirstTwoEmbedding_staticTransverseSliceOffset_mem_box hd hk hyRectangle
  have hvBox := cubicMetricBox_epsilonGoodBlockCenter_subset_scaled_box hyCoarse
    (cubicBoxFace_subset_cubicMetricBox hv)
  rw [mem_cubicBoxFace] at hv ⊢
  constructor
  · have hy0 := (mem_squareRectangleRight_iff.mp hy).1
    have hcoord := hv.1
    simp [epsilonGoodBlockCenter, cubicScale, cubicTranslatedFirstTwoEmbedding,
      cubicTranslate, cubicOrigin, staticTransverseSliceOffset, cubicEmbed, hy0,
      Nat.cast_mul, Nat.cast_add] at hcoord ⊢
    nlinarith
  · intro j _hji
    exact (mem_cubicMetricBox.mp hvBox j)

/-- A successful translated good-block slice gives a literal left-right crossing of the
ambient physical box of radius `N(K+1)`. -/
theorem mem_cubicBoxCrossingEvent_of_mem_goodBond_staticTransverseSliceCrossing
    {d N K : ℕ} (hd : 2 ≤ d) (p : I) (ε : ℝ)
    {k : Cubic (d - 2)} (hk : k ∈ staticTransverseSliceIndices d K)
    {ω : EdgeConfiguration d}
    (hcross : ω ∈ epsilonGoodBondTranslatedSliceCrossingEvent
      d hd p ε N (staticTransverseSliceOffset d K k) (2 * K) K) :
    ω ∈ cubicBoxCrossingEvent d (N * (K + 1)) (Fin.castLE hd 0) := by
  obtain ⟨x, hx, y, hy, u, hu, v, hv, huv⟩ :=
    exists_connectionEventIn_between_faces_of_mem_goodBondTranslatedSliceCrossing
      hd p ε N (2 * K) K (staticTransverseSliceOffset d K k) ω hcross
  have huBig := left_endpoint_staticTransverseSlice_mem_scaled_boxFace hd hk hx hu
  have hvBig := right_endpoint_staticTransverseSlice_mem_scaled_boxFace hd hk hy hv
  have huvBig : ω ∈ connectionEventIn d
      (cubicBoxEdges d cubicOrigin (N * (K + 1))) u v :=
    connectionEventIn_mono
      (epsilonGoodBondTranslatedSliceCrossingSupport_static_subset_cubicBoxEdges hd hk)
      u v huv
  simp only [cubicBoxCrossingEvent, Set.mem_iUnion]
  exact ⟨u, huBig, v, hvBig, huvBig⟩

/-- Equation (7.74) in its ambient-box form: at the lower density, failure of a left-right
crossing of `B(N(K+1))` is exponentially small in `K` times the number of independent
transverse slices. -/
theorem one_sub_cubicBoxCrossing_probability_le_exp_staticTransverse
    {d : ℕ} (hd : 3 ≤ d) (p q : I) (ε : ℝ)
    (N K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p ε N).real
          {η : Set (Cubic d) | cubicOrigin ∈ η}) :
    1 - (bernoulliBondMeasure d p).real
        (cubicBoxCrossingEvent d (N * (K + 1)) (Fin.castLE (by omega) 0)) ≤
      Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ) *
        ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) := by
  let A := cubicBoxCrossingEvent d (N * (K + 1)) (Fin.castLE (by omega) 0)
  let failures : Set (EdgeConfiguration d) :=
    ⋂ k : {k : Cubic (d - 2) // k ∈ staticTransverseSliceIndices d K},
      (epsilonGoodBondTranslatedSliceCrossingEvent
        d (by omega) p ε N (staticTransverseSliceOffset d K k.1) (2 * K) K)ᶜ
  have hsubset : Aᶜ ⊆ failures := by
    intro ω hω
    simp only [failures, Set.mem_iInter, Set.mem_compl_iff]
    intro k hkSuccess
    exact hω (mem_cubicBoxCrossingEvent_of_mem_goodBond_staticTransverseSliceCrossing
      (by omega) p ε k.2 hkSuccess)
  have hfail := staticTransverseSlice_all_fail_probability_le_exp
    hd p q ε N K hN hK hq hqThreshold hmarginal
  have hcomp : 1 - (bernoulliBondMeasure d p).real A =
      (bernoulliBondMeasure d p).real Aᶜ := by
    rw [probReal_compl_eq_one_sub (measurableSet_cubicBoxCrossingEvent
      d (N * (K + 1)) (Fin.castLE (by omega) 0))]
  rw [hcomp]
  exact (measureReal_mono hsubset).trans (by simpa [failures] using hfail)

/-! ### Finite-box terminal Menger interface -/

/-- Vertices of `B(r)` as a finite subtype. -/
abbrev CubicBoxVertex (d r : ℕ) :=
  {x : Cubic d // x ∈ cubicMetricBox d cubicOrigin r}

/-- The induced open graph on `B(r)`. -/
noncomputable def cubicBoxOpenGraph (d r : ℕ) (ω : EdgeConfiguration d) :
    SimpleGraph (CubicBoxVertex d r) :=
  finiteBoxOpenGraph d ω cubicOrigin r

/-- A chosen signed face, viewed as terminals of the finite induced open graph. -/
noncomputable def cubicBoxFaceTerminals
    (d r : ℕ) (i : Fin d) (positive : Bool) : Finset (CubicBoxVertex d r) :=
  Finset.univ.filter fun x ↦ x.1 ∈ cubicBoxFace d cubicOrigin r i positive

@[simp]
theorem mem_cubicBoxFaceTerminals
    {d r : ℕ} {i : Fin d} {positive : Bool} {x : CubicBoxVertex d r} :
    x ∈ cubicBoxFaceTerminals d r i positive ↔
      x.1 ∈ cubicBoxFace d cubicOrigin r i positive := by
  simp [cubicBoxFaceTerminals]

/-- Forget the finite-box subtype while retaining open adjacency. -/
noncomputable def cubicBoxOpenGraphToOpenHom
    (d r : ℕ) (ω : EdgeConfiguration d) :
    cubicBoxOpenGraph d r ω →g cubicOpenGraph d ω where
  toFun := Subtype.val
  map_rel' := SimpleGraph.induce_adj.mp

/-- Ambient cubic walk represented by a walk of the finite induced open graph. -/
noncomputable def ambientWalkOfCubicBoxOpenWalk
    {d r : ℕ} {ω : EdgeConfiguration d} {x y : CubicBoxVertex d r}
    (w : (cubicBoxOpenGraph d r ω).Walk x y) :
    (cubicGraph d).Walk x.1 y.1 :=
  (w.map (cubicBoxOpenGraphToOpenHom d r ω)).map (cubicOpenGraphHom d ω)

theorem walkIsOpen_ambientWalkOfCubicBoxOpenWalk
    {d r : ℕ} {ω : EdgeConfiguration d} {x y : CubicBoxVertex d r}
    (w : (cubicBoxOpenGraph d r ω).Walk x y) :
    walkIsOpen ω (ambientWalkOfCubicBoxOpenWalk w) :=
  walkIsOpen_map_cubicOpenGraphHom (w.map (cubicBoxOpenGraphToOpenHom d r ω))

theorem support_ambientWalkOfCubicBoxOpenWalk_subset
    {d r : ℕ} {ω : EdgeConfiguration d} {x y : CubicBoxVertex d r}
    (w : (cubicBoxOpenGraph d r ω).Walk x y) :
    ∀ z ∈ (ambientWalkOfCubicBoxOpenWalk w).support,
      z ∈ cubicMetricBox d cubicOrigin r := by
  intro z hz
  let wOpen := w.map (cubicBoxOpenGraphToOpenHom d r ω)
  have hsAmbient : (ambientWalkOfCubicBoxOpenWalk w).support =
      wOpen.support.map (cubicOpenGraphHom d ω) := by
    simpa [ambientWalkOfCubicBoxOpenWalk, wOpen] using
      (SimpleGraph.Walk.support_map (cubicOpenGraphHom d ω) wOpen)
  have hzOpenMap : z ∈ wOpen.support.map (cubicOpenGraphHom d ω) :=
    (congrArg (fun l ↦ z ∈ l) hsAmbient).mp hz
  obtain ⟨zOpen, hzOpen, hzEq⟩ := List.mem_map.mp hzOpenMap
  have hzEq' : zOpen = z := by simpa [cubicOpenGraphHom] using hzEq
  subst zOpen
  have hsOpen : wOpen.support =
      w.support.map (cubicBoxOpenGraphToOpenHom d r ω) :=
    SimpleGraph.Walk.support_map (cubicBoxOpenGraphToOpenHom d r ω) w
  have hzSubtypeMap : z ∈ w.support.map (cubicBoxOpenGraphToOpenHom d r ω) :=
    (congrArg (fun l ↦ z ∈ l) hsOpen).mp hzOpen
  obtain ⟨zBox, _hzBox, hzBoxEq⟩ := List.mem_map.mp hzSubtypeMap
  have : zBox.1 = z := by simpa [cubicBoxOpenGraphToOpenHom] using hzBoxEq
  rw [← this]
  exact zBox.2

theorem edge_subset_ambientWalkOfCubicBoxOpenWalk
    {d r : ℕ} {ω : EdgeConfiguration d} {x y : CubicBoxVertex d r}
    (w : (cubicBoxOpenGraph d r ω).Walk x y) :
    walkEdgeFinset (ambientWalkOfCubicBoxOpenWalk w) ⊆
      cubicBoxEdges d cubicOrigin r :=
  walkEdgeFinset_subset_cubicBoxEdges_of_support _
    (support_ambientWalkOfCubicBoxOpenWalk_subset w)

/-- A terminal walk in the finite open box yields a source-facing crossing event witness. -/
theorem mem_cubicBoxCrossingEvent_of_walkBetweenFinsets
    {d r : ℕ} {i : Fin d} {ω : EdgeConfiguration d}
    (P : EdgeMenger.WalkBetweenFinsets (cubicBoxOpenGraph d r ω)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true)) :
    ω ∈ cubicBoxCrossingEvent d r i := by
  let w := ambientWalkOfCubicBoxOpenWalk P.walk
  have hopen := walkIsOpen_ambientWalkOfCubicBoxOpenWalk P.walk
  have hedges := edge_subset_ambientWalkOfCubicBoxOpenWalk P.walk
  simp only [cubicBoxCrossingEvent, Set.mem_iUnion]
  exact ⟨P.start.1.1, mem_cubicBoxFaceTerminals.mp P.start.2,
    P.finish.1.1, mem_cubicBoxFaceTerminals.mp P.finish.2, w, hopen, hedges⟩

/-- A source-facing box crossing becomes a terminal walk in the induced finite open graph. -/
theorem exists_walkBetweenFinsets_of_mem_cubicBoxCrossingEvent
    {d r : ℕ} {i : Fin d} {ω : EdgeConfiguration d}
    (hω : ω ∈ cubicBoxCrossingEvent d r i) :
    Nonempty (EdgeMenger.WalkBetweenFinsets (cubicBoxOpenGraph d r ω)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true)) := by
  simp only [cubicBoxCrossingEvent, Set.mem_iUnion] at hω
  obtain ⟨x, hx, y, hy, w, hwOpen, hwEdges⟩ := hω
  have hxBox := cubicBoxFace_subset_cubicMetricBox hx
  have hsupport := walk_support_subset_cubicMetricBox_of_edges hxBox w hwEdges
  obtain ⟨q⟩ := nonempty_finiteBoxOpenGraph_walk_of_walkIsOpen_of_support
    w hwOpen hsupport
  let start : {v : CubicBoxVertex d r // v ∈ cubicBoxFaceTerminals d r i false} :=
    ⟨⟨x, hxBox⟩, mem_cubicBoxFaceTerminals.mpr hx⟩
  let finish : {v : CubicBoxVertex d r // v ∈ cubicBoxFaceTerminals d r i true} :=
    ⟨⟨y, cubicBoxFace_subset_cubicMetricBox hy⟩,
      mem_cubicBoxFaceTerminals.mpr hy⟩
  let P : EdgeMenger.WalkBetweenFinsets (cubicBoxOpenGraph d r ω)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true) :=
    { start := start
      finish := finish
      walk := q.copy rfl rfl }
  exact ⟨P⟩

/-- One box crossing is equivalent to one unit of finite terminal-set edge reachability. -/
theorem mem_cubicBoxCrossingEvent_iff_isEdgeReachableBetweenFinsets_one
    {d r : ℕ} {i : Fin d} {ω : EdgeConfiguration d} :
    ω ∈ cubicBoxCrossingEvent d r i ↔
      EdgeMenger.IsEdgeReachableBetweenFinsets (cubicBoxOpenGraph d r ω) 1
        (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true) := by
  rw [EdgeMenger.isEdgeReachableBetweenFinsets_iff_exists_pairwise_edgeDisjoint_walks]
  constructor
  · intro hω
    obtain ⟨P⟩ := exists_walkBetweenFinsets_of_mem_cubicBoxCrossingEvent hω
    refine ⟨fun _ ↦ P, ?_⟩
    intro a b hab
    exact (hab (Subsingleton.elim a b)).elim
  · rintro ⟨P, _hP⟩
    exact mem_cubicBoxCrossingEvent_of_walkBetweenFinsets (P (0 : Fin 1))

/-- Monotonicity of the induced finite-box open graph under inclusion of bond
configurations. -/
noncomputable def cubicBoxOpenGraphMonoHom {d r : ℕ}
    {ω η : EdgeConfiguration d} (hωη : ω ⊆ η) :
    cubicBoxOpenGraph d r ω →g cubicBoxOpenGraph d r η where
  toFun := id
  map_rel' := by
    intro x y hxy
    apply SimpleGraph.induce_adj.mpr
    obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp (SimpleGraph.induce_adj.mp hxy)
    exact cubicOpenGraph_adj.mpr ⟨hadj, hωη hopen⟩

/-- The ambient cubic edge represented by an edge of the finite-box open graph. -/
noncomputable def cubicEdgeOfBoxOpenEdge {d r : ℕ} {ω : EdgeConfiguration d}
    (e : (cubicBoxOpenGraph d r ω).edgeSet) : CubicEdge d := by
  let f : cubicBoxOpenGraph d r ω →g cubicGraph d :=
    (cubicOpenGraphHom d ω).comp (cubicBoxOpenGraphToOpenHom d r ω)
  exact ⟨Sym2.map f e.1, f.map_mem_edgeSet e.2⟩

theorem cubicEdgeOfBoxOpenEdge_val {d r : ℕ} {ω : EdgeConfiguration d}
    (e : (cubicBoxOpenGraph d r ω).edgeSet) :
    (cubicEdgeOfBoxOpenEdge e : Sym2 (Cubic d)) =
      Sym2.map Subtype.val e.1 := by
  apply Sym2.map_congr
  intro x _hx
  rfl

theorem cubicEdgeOfBoxOpenEdge_injective {d r : ℕ}
    {ω : EdgeConfiguration d} :
    Function.Injective (cubicEdgeOfBoxOpenEdge
      (d := d) (r := r) (ω := ω)) := by
  intro e f hef
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  have hval := congrArg (fun q : CubicEdge d ↦ (q : Sym2 (Cubic d))) hef
  simpa [cubicEdgeOfBoxOpenEdge_val] using hval

theorem cubicEdgeOfBoxOpenEdge_mem_configuration {d r : ℕ}
    {ω : EdgeConfiguration d}
    (e : (cubicBoxOpenGraph d r ω).edgeSet) :
    cubicEdgeOfBoxOpenEdge e ∈ ω := by
  let u := e.1.out.1
  let v := e.1.out.2
  have hadjBox : (cubicBoxOpenGraph d r ω).Adj u v := by
    rw [← SimpleGraph.mem_edgeSet]
    change s(e.1.out.1, e.1.out.2) ∈ (cubicBoxOpenGraph d r ω).edgeSet
    exact (congrArg (fun q ↦ q ∈ (cubicBoxOpenGraph d r ω).edgeSet)
      e.1.out_eq).mpr e.2
  obtain ⟨hadj, hopen⟩ := cubicOpenGraph_adj.mp
    (SimpleGraph.induce_adj.mp hadjBox)
  have heq : cubicEdgeOfBoxOpenEdge e =
      (⟨s(u.1, v.1), (SimpleGraph.mem_edgeSet (cubicGraph d)).mpr hadj⟩ : CubicEdge d) := by
    apply Subtype.ext
    rw [cubicEdgeOfBoxOpenEdge_val]
    calc
      Sym2.map Subtype.val e.1 =
          Sym2.map Subtype.val s(e.1.out.1, e.1.out.2) :=
        congrArg (Sym2.map Subtype.val) e.1.out_eq.symm
      _ = s(u.1, v.1) := by rfl
  rw [heq]
  exact hopen

noncomputable def cubicEdgeOfBoxOpenEdgeEmbedding {d r : ℕ}
    {ω : EdgeConfiguration d} :
    (cubicBoxOpenGraph d r ω).edgeSet ↪ CubicEdge d where
  toFun := cubicEdgeOfBoxOpenEdge
  inj' := cubicEdgeOfBoxOpenEdge_injective

theorem edges_ambientWalkOfCubicBoxOpenWalk
    {d r : ℕ} {ω : EdgeConfiguration d} {x y : CubicBoxVertex d r}
    (w : (cubicBoxOpenGraph d r ω).Walk x y) :
    (ambientWalkOfCubicBoxOpenWalk w).edges =
      w.edges.map (Sym2.map Subtype.val) := by
  let h := cubicBoxOpenGraphToOpenHom d r ω
  let q := w.map h
  have hq : (q.map (cubicOpenGraphHom d ω)).edges =
      q.edges.map (Sym2.map (cubicOpenGraphHom d ω)) :=
    SimpleGraph.Walk.edges_map (cubicOpenGraphHom d ω) q
  have hw : q.edges = w.edges.map (Sym2.map h) :=
    SimpleGraph.Walk.edges_map h w
  calc
    (ambientWalkOfCubicBoxOpenWalk w).edges =
        q.edges.map (Sym2.map (cubicOpenGraphHom d ω)) := by
      simpa [ambientWalkOfCubicBoxOpenWalk, q, h] using hq
    _ = (w.edges.map (Sym2.map h)).map
        (Sym2.map (cubicOpenGraphHom d ω)) := by rw [hw]
    _ = w.edges.map (Sym2.map Subtype.val) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _he
      change Sym2.map (cubicOpenGraphHom d ω) (Sym2.map h e) =
        Sym2.map Subtype.val e
      rw [Sym2.map_map]
      apply Sym2.map_congr
      intro z _hz
      rfl

/-! The next two lemmas identify the crossing event's Hamming interior with finite
set-to-set edge reachability.  This is the cubic-box form of Grimmett Lemma 11.22. -/

/-- A configuration in the depth-`s` box-crossing interior survives every cut of fewer than
`s+1` edges in the finite induced open graph. -/
theorem mem_interiorDepth_cubicBoxCrossingEvent_imp_isEdgeReachableBetweenFinsets
    {d r s : ℕ} {i : Fin d} {ω : EdgeConfiguration d}
    (hω : ω ∈ interiorDepth s (cubicBoxCrossingEvent d r i)) :
    EdgeMenger.IsEdgeReachableBetweenFinsets (cubicBoxOpenGraph d r ω) (s + 1)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true) := by
  classical
  rw [(isIncreasingEvent_cubicBoxCrossingEvent d r i).mem_interiorDepth_iff_diff_finset]
    at hω
  intro cut hcut
  let H := cubicBoxOpenGraph d r ω
  have hcutFinite : cut.Finite := Set.finite_of_encard_le_coe hcut.le
  let R : Finset H.edgeSet := Finset.univ.filter fun e ↦ e.1 ∈ cut
  let edgeValEmbedding : H.edgeSet ↪ Sym2 (CubicBoxVertex d r) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hRsubset : R.map edgeValEmbedding ⊆ hcutFinite.toFinset := by
    intro e he
    obtain ⟨eH, heHR, rfl⟩ := Finset.mem_map.mp he
    have heCut : eH.1 ∈ cut := (Finset.mem_filter.mp heHR).2
    simpa using heCut
  have hRcard : R.card ≤ hcutFinite.toFinset.card := by
    rw [← Finset.card_map edgeValEmbedding]
    exact Finset.card_le_card hRsubset
  have hcutCard : hcutFinite.toFinset.card < s + 1 := by
    rw [← ENat.coe_lt_coe, ← hcutFinite.encard_eq_coe_toFinset_card]
    exact hcut
  let D : Finset (CubicEdge d) := R.map cubicEdgeOfBoxOpenEdgeEmbedding
  have hD : D.card ≤ s := by
    have hDR : D.card = R.card := Finset.card_map _
    omega
  have hcross : ω \ (D : Set (CubicEdge d)) ∈ cubicBoxCrossingEvent d r i := hω D hD
  obtain ⟨Pη⟩ := exists_walkBetweenFinsets_of_mem_cubicBoxCrossingEvent hcross
  have hηω : ω \ (D : Set (CubicEdge d)) ⊆ ω := Set.diff_subset
  let φ := cubicBoxOpenGraphMonoHom (d := d) (r := r) hηω
  let P : EdgeMenger.WalkBetweenFinsets H
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true) :=
    { start := Pη.start
      finish := Pη.finish
      walk := Pη.walk.map φ }
  refine ⟨P.start.1, P.start.2, P.finish.1, P.finish.2, P.walk, ?_⟩
  intro e he
  have hmapEdges : P.walk.edges = Pη.walk.edges.map (Sym2.map φ) :=
    SimpleGraph.Walk.edges_map φ Pη.walk
  have heMap : e ∈ Pη.walk.edges.map (Sym2.map φ) :=
    (congrArg (fun l ↦ e ∈ l) hmapEdges).mp he
  obtain ⟨eη, heη, heηmap⟩ := List.mem_map.mp heMap
  have heEq : eη = e := by
    simpa [φ, cubicBoxOpenGraphMonoHom] using heηmap
  subst eη
  intro heCut
  have heEdgeH : e ∈ H.edgeSet := P.walk.edges_subset_edgeSet he
  let eH : H.edgeSet := ⟨e, heEdgeH⟩
  have heHR : eH ∈ R := by
    change eH ∈ Finset.univ.filter fun q : H.edgeSet ↦ q.1 ∈ cut
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heCut⟩
  have heD : cubicEdgeOfBoxOpenEdge eH ∈ D :=
    Finset.mem_map.mpr ⟨eH, heHR, rfl⟩
  have heEdgeη : e ∈ (cubicBoxOpenGraph d r
      (ω \ (D : Set (CubicEdge d)))).edgeSet := Pη.walk.edges_subset_edgeSet heη
  let eEta : (cubicBoxOpenGraph d r
      (ω \ (D : Set (CubicEdge d)))).edgeSet := ⟨e, heEdgeη⟩
  have hopenEta : cubicEdgeOfBoxOpenEdge eEta ∈
      ω \ (D : Set (CubicEdge d)) :=
    cubicEdgeOfBoxOpenEdge_mem_configuration eEta
  have hedgeEq : cubicEdgeOfBoxOpenEdge eEta = cubicEdgeOfBoxOpenEdge eH := by
    apply Subtype.ext
    rw [cubicEdgeOfBoxOpenEdge_val, cubicEdgeOfBoxOpenEdge_val]
  exact hopenEta.2 (hedgeEq ▸ heD)

/-- Conversely, cut-survival in the finite open box puts the original configuration in the
corresponding Hamming interior of the source-facing crossing event. -/
theorem isEdgeReachableBetweenFinsets_imp_mem_interiorDepth_cubicBoxCrossingEvent
    {d r s : ℕ} {i : Fin d} {ω : EdgeConfiguration d}
    (hreach : EdgeMenger.IsEdgeReachableBetweenFinsets
      (cubicBoxOpenGraph d r ω) (s + 1)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true)) :
    ω ∈ interiorDepth s (cubicBoxCrossingEvent d r i) := by
  classical
  rw [(isIncreasingEvent_cubicBoxCrossingEvent d r i).mem_interiorDepth_iff_diff_finset]
  intro D hD
  let H := cubicBoxOpenGraph d r ω
  let R : Finset H.edgeSet :=
    Finset.univ.filter fun e ↦ cubicEdgeOfBoxOpenEdge e ∈ D
  have hRsubset : R.map cubicEdgeOfBoxOpenEdgeEmbedding ⊆ D := by
    intro e he
    obtain ⟨eH, heHR, rfl⟩ := Finset.mem_map.mp he
    exact (Finset.mem_filter.mp heHR).2
  have hRcard : R.card ≤ D.card := by
    rw [← Finset.card_map cubicEdgeOfBoxOpenEdgeEmbedding]
    exact Finset.card_le_card hRsubset
  let edgeValEmbedding : H.edgeSet ↪ Sym2 (CubicBoxVertex d r) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let deletedEdges : Set (Sym2 (CubicBoxVertex d r)) :=
    (R.map edgeValEmbedding : Finset (Sym2 (CubicBoxVertex d r)))
  have hcut : deletedEdges.encard < (s + 1 : ℕ) := by
    change ((R.map edgeValEmbedding : Finset (Sym2 (CubicBoxVertex d r))) :
      Set (Sym2 (CubicBoxVertex d r))).encard < (s + 1 : ℕ)
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_map]
    exact_mod_cast (lt_of_le_of_lt hRcard (by omega : D.card < s + 1))
  obtain ⟨x, hx, y, hy, w, hwAvoid⟩ := hreach deletedEdges hcut
  let wAmbient := ambientWalkOfCubicBoxOpenWalk w
  have hwOpen : walkIsOpen (ω \ (D : Set (CubicEdge d))) wAmbient := by
    intro e he
    have heOpen : (⟨e, wAmbient.edges_subset_edgeSet he⟩ : CubicEdge d) ∈ ω :=
      walkIsOpen_ambientWalkOfCubicBoxOpenWalk w e he
    refine ⟨heOpen, ?_⟩
    intro heD
    have heMap : e ∈ w.edges.map (Sym2.map Subtype.val) := by
      rw [← edges_ambientWalkOfCubicBoxOpenWalk]
      exact he
    obtain ⟨e₀, he₀, he₀map⟩ := List.mem_map.mp heMap
    have heEdgeH : e₀ ∈ H.edgeSet := w.edges_subset_edgeSet he₀
    let eH : H.edgeSet := ⟨e₀, heEdgeH⟩
    have hedgeEq : cubicEdgeOfBoxOpenEdge eH =
        (⟨e, wAmbient.edges_subset_edgeSet he⟩ : CubicEdge d) := by
      apply Subtype.ext
      rw [cubicEdgeOfBoxOpenEdge_val]
      exact he₀map
    have heHR : eH ∈ R := by
      change eH ∈ Finset.univ.filter fun q : H.edgeSet ↦ cubicEdgeOfBoxOpenEdge q ∈ D
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedgeEq ▸ heD⟩
    have heCut : e₀ ∈ deletedEdges := by
      change e₀ ∈ R.map edgeValEmbedding
      exact Finset.mem_map.mpr ⟨eH, heHR, rfl⟩
    exact hwAvoid e₀ he₀ heCut
  simp only [cubicBoxCrossingEvent, Set.mem_iUnion]
  exact ⟨x.1, mem_cubicBoxFaceTerminals.mp hx, y.1,
    mem_cubicBoxFaceTerminals.mp hy, wAmbient, hwOpen,
    edge_subset_ambientWalkOfCubicBoxOpenWalk w⟩

/-- **Cubic-box interior-depth/Menger adapter.** Depth `s` in the crossing event is exactly
survival after every cut of fewer than `s+1` finite-box edges. -/
theorem mem_interiorDepth_cubicBoxCrossingEvent_iff
    (d r s : ℕ) (i : Fin d) (ω : EdgeConfiguration d) :
    ω ∈ interiorDepth s (cubicBoxCrossingEvent d r i) ↔
      EdgeMenger.IsEdgeReachableBetweenFinsets (cubicBoxOpenGraph d r ω) (s + 1)
        (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true) := by
  exact ⟨mem_interiorDepth_cubicBoxCrossingEvent_imp_isEdgeReachableBetweenFinsets,
    isEdgeReachableBetweenFinsets_imp_mem_interiorDepth_cubicBoxCrossingEvent⟩

/-- There are `k` pairwise edge-disjoint open crossings of `B(r)` in direction `i`, encoded
as paths in the finite induced open graph.  The ambient-walk lemmas above show this encoding is
exactly the source's bond-path notion. -/
def HasEdgeDisjointCubicBoxCrossings
    (d r : ℕ) (i : Fin d) (k : ℕ) (ω : EdgeConfiguration d) : Prop :=
  ∃ P : Fin k → EdgeMenger.WalkBetweenFinsets (cubicBoxOpenGraph d r ω)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true),
    Pairwise fun a b ↦ (P a).walk.edges.Disjoint (P b).walk.edges

theorem hasEdgeDisjointCubicBoxCrossings_iff_isEdgeReachableBetweenFinsets
    (d r : ℕ) (i : Fin d) (k : ℕ) (ω : EdgeConfiguration d) :
    HasEdgeDisjointCubicBoxCrossings d r i k ω ↔
      EdgeMenger.IsEdgeReachableBetweenFinsets (cubicBoxOpenGraph d r ω) k
        (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true) :=
  EdgeMenger.isEdgeReachableBetweenFinsets_iff_exists_pairwise_edgeDisjoint_walks.symm

theorem hasEdgeDisjointCubicBoxCrossings_zero
    (d r : ℕ) (i : Fin d) (ω : EdgeConfiguration d) :
    HasEdgeDisjointCubicBoxCrossings d r i 0 ω := by
  refine ⟨fun x ↦ Fin.elim0 x, ?_⟩
  intro x
  exact Fin.elim0 x

private theorem cubicBox_terminalWalk_start_ne_finish
    {d r : ℕ} {i : Fin d} (hr : 1 ≤ r) {ω : EdgeConfiguration d}
    (P : EdgeMenger.WalkBetweenFinsets (cubicBoxOpenGraph d r ω)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true)) :
    P.start.1 ≠ P.finish.1 := by
  intro h
  have hs := (mem_cubicBoxFace.mp (mem_cubicBoxFaceTerminals.mp P.start.2)).1
  have ht := (mem_cubicBoxFace.mp (mem_cubicBoxFaceTerminals.mp P.finish.2)).1
  have hval : P.start.1.1 = P.finish.1.1 := congrArg Subtype.val h
  have hcoord := congrFun hval i
  simp [cubicOrigin] at hs ht
  omega

private theorem cubicBox_terminalWalk_edges_nonempty
    {d r : ℕ} {i : Fin d} (hr : 1 ≤ r) {ω : EdgeConfiguration d}
    (P : EdgeMenger.WalkBetweenFinsets (cubicBoxOpenGraph d r ω)
      (cubicBoxFaceTerminals d r i false) (cubicBoxFaceTerminals d r i true)) :
    P.walk.edges ≠ [] := by
  exact SimpleGraph.Walk.edges_eq_nil.not.mpr
    (SimpleGraph.Walk.not_nil_of_ne (cubicBox_terminalWalk_start_ne_finish hr P))

/-- A disjoint crossing family is bounded by the finite number of unordered pairs of box
vertices.  This coarse uniform bound is used only to define the maximum. -/
theorem hasEdgeDisjointCubicBoxCrossings_le_pair_card
    {d r k : ℕ} {i : Fin d} (hr : 1 ≤ r) {ω : EdgeConfiguration d}
    (h : HasEdgeDisjointCubicBoxCrossings d r i k ω) :
    k ≤ Fintype.card (Sym2 (CubicBoxVertex d r)) := by
  classical
  obtain ⟨P, hP⟩ := h
  have hedge (a : Fin k) : ∃ e, e ∈ (P a).walk.edges :=
    List.exists_mem_of_ne_nil _ (cubicBox_terminalWalk_edges_nonempty hr (P a))
  let chosen : Fin k → Sym2 (CubicBoxVertex d r) :=
    fun a ↦ Classical.choose (hedge a)
  have chosen_mem (a : Fin k) : chosen a ∈ (P a).walk.edges :=
    Classical.choose_spec (hedge a)
  have hinj : Function.Injective chosen := by
    intro a b hab
    by_contra hne
    exact List.disjoint_left.mp (hP hne) (chosen_mem a) (hab ▸ chosen_mem b)
  simpa using Fintype.card_le_of_injective chosen hinj

/-- The maximal number of pairwise edge-disjoint open crossings of `B(r)` in direction `i`.
It is set to zero at `r=0`, where the two signed faces coincide. -/
noncomputable def maxEdgeDisjointLeftRightCrossings
    (d r : ℕ) (i : Fin d) (ω : EdgeConfiguration d) : ℕ := by
  classical
  exact if r = 0 then 0 else
    Nat.findGreatest (fun k ↦ HasEdgeDisjointCubicBoxCrossings d r i k ω)
      (Fintype.card (Sym2 (CubicBoxVertex d r)))

@[simp]
theorem maxEdgeDisjointLeftRightCrossings_zero
    (d : ℕ) (i : Fin d) (ω : EdgeConfiguration d) :
    maxEdgeDisjointLeftRightCrossings d 0 i ω = 0 := by
  simp [maxEdgeDisjointLeftRightCrossings]

theorem hasEdgeDisjointCubicBoxCrossings_max
    (d r : ℕ) (i : Fin d) (hr : 1 ≤ r) (ω : EdgeConfiguration d) :
    HasEdgeDisjointCubicBoxCrossings d r i
      (maxEdgeDisjointLeftRightCrossings d r i ω) ω := by
  classical
  rw [maxEdgeDisjointLeftRightCrossings, if_neg (Nat.ne_of_gt hr)]
  exact Nat.findGreatest_spec
    (P := fun k ↦ HasEdgeDisjointCubicBoxCrossings d r i k ω)
    (m := 0) (Nat.zero_le _) (hasEdgeDisjointCubicBoxCrossings_zero d r i ω)

theorem hasEdgeDisjointCubicBoxCrossings_iff_le_max
    {d r k : ℕ} {i : Fin d} (hr : 1 ≤ r) (ω : EdgeConfiguration d) :
    HasEdgeDisjointCubicBoxCrossings d r i k ω ↔
      k ≤ maxEdgeDisjointLeftRightCrossings d r i ω := by
  classical
  constructor
  · intro hk
    by_contra hnot
    have hlt : maxEdgeDisjointLeftRightCrossings d r i ω < k := Nat.lt_of_not_ge hnot
    rw [maxEdgeDisjointLeftRightCrossings, if_neg (Nat.ne_of_gt hr)] at hlt
    exact (Nat.findGreatest_is_greatest
      (P := fun j ↦ HasEdgeDisjointCubicBoxCrossings d r i j ω) hlt
      (hasEdgeDisjointCubicBoxCrossings_le_pair_card hr hk)) hk
  · intro hk
    obtain ⟨P, hP⟩ := hasEdgeDisjointCubicBoxCrossings_max d r i hr ω
    let ι : Fin k → Fin (maxEdgeDisjointLeftRightCrossings d r i ω) := Fin.castLE hk
    refine ⟨fun a ↦ P (ι a), ?_⟩
    intro a b hab
    apply hP
    intro heq
    exact hab (Fin.castLE_injective hk heq)

@[simp]
theorem maxEdgeDisjointLeftRightCrossings_empty
    {d r : ℕ} {i : Fin d} (hr : 1 ≤ r) :
    maxEdgeDisjointLeftRightCrossings d r i (∅ : EdgeConfiguration d) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  obtain ⟨P, _hP⟩ := hasEdgeDisjointCubicBoxCrossings_max
    d r i hr (∅ : EdgeConfiguration d)
  let a : Fin (maxEdgeDisjointLeftRightCrossings d r i (∅ : EdgeConfiguration d)) :=
    ⟨0, hpos⟩
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _
    (cubicBox_terminalWalk_edges_nonempty hr (P a))
  let eH : (cubicBoxOpenGraph d r (∅ : EdgeConfiguration d)).edgeSet :=
    ⟨e, (P a).walk.edges_subset_edgeSet he⟩
  have hopen := cubicEdgeOfBoxOpenEdge_mem_configuration eH
  exact hopen

theorem mem_interiorDepth_cubicBoxCrossingEvent_iff_le_max
    {d r s : ℕ} {i : Fin d} (hr : 1 ≤ r) (ω : EdgeConfiguration d) :
    ω ∈ interiorDepth s (cubicBoxCrossingEvent d r i) ↔
      s + 1 ≤ maxEdgeDisjointLeftRightCrossings d r i ω := by
  rw [mem_interiorDepth_cubicBoxCrossingEvent_iff,
    ← hasEdgeDisjointCubicBoxCrossings_iff_isEdgeReachableBetweenFinsets,
    hasEdgeDisjointCubicBoxCrossings_iff_le_max hr]

theorem measurableSet_maxEdgeDisjointLeftRightCrossings_le
    {d r s : ℕ} {i : Fin d} (hr : 1 ≤ r) :
    MeasurableSet
      {ω | maxEdgeDisjointLeftRightCrossings d r i ω ≤ s} := by
  have hset : {ω | maxEdgeDisjointLeftRightCrossings d r i ω ≤ s} =
      (interiorDepth s (cubicBoxCrossingEvent d r i))ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
      mem_interiorDepth_cubicBoxCrossingEvent_iff_le_max hr,
      not_le, Nat.lt_add_one_iff]
  rw [hset]
  exact (measurableSet_interiorDepth
    (measurableSet_cubicBoxCrossingEvent d r i) s).compl

theorem measurableSet_cast_maxEdgeDisjointLeftRightCrossings_ge
    {d r : ℕ} {i : Fin d} (hr : 1 ≤ r) (t : ℝ) :
    MeasurableSet
      {ω | t ≤ (maxEdgeDisjointLeftRightCrossings d r i ω : ℝ)} := by
  have hset : {ω | t ≤ (maxEdgeDisjointLeftRightCrossings d r i ω : ℝ)} =
      {ω | ⌈t⌉₊ ≤ maxEdgeDisjointLeftRightCrossings d r i ω} := by
    ext ω
    exact (Nat.ceil_le (α := ℝ)).symm
  rw [hset]
  cases hceil : ⌈t⌉₊ with
  | zero => simp
  | succ s =>
      have hthreshold : {ω | Nat.succ s ≤
          maxEdgeDisjointLeftRightCrossings d r i ω} =
          interiorDepth s (cubicBoxCrossingEvent d r i) := by
        ext ω
        exact (mem_interiorDepth_cubicBoxCrossingEvent_iff_le_max hr ω).symm
      rw [hthreshold]
      exact measurableSet_interiorDepth
        (measurableSet_cubicBoxCrossingEvent d r i) s

/-! ### Sprinkling and the quantitative form of equation (7.75) -/

/-- ACCFR sprinkling after the cubic-box Menger identification. -/
theorem one_sub_bernoulliBondMeasure_real_cubicBox_maxCrossings_ge_le
    {d r s : ℕ} {i : Fin d} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) :
    1 - (bernoulliBondMeasure d p₂).real
        {ω | s + 1 ≤ maxEdgeDisjointLeftRightCrossings d r i ω} ≤
      ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)) ^ s *
        (1 - (bernoulliBondMeasure d p₁).real (cubicBoxCrossingEvent d r i)) := by
  have hset : interiorDepth s (cubicBoxCrossingEvent d r i) =
      {ω | s + 1 ≤ maxEdgeDisjointLeftRightCrossings d r i ω} := by
    ext ω
    exact mem_interiorDepth_cubicBoxCrossingEvent_iff_le_max hr ω
  rw [← hset]
  exact IsIncreasingEvent.one_sub_bernoulliBondMeasure_real_interiorDepth_le
    (isIncreasingEvent_cubicBoxCrossingEvent d r i)
    (measurableSet_cubicBoxCrossingEvent d r i) h12 hs

/-- Complement form: at the higher density, the probability of at most `s` disjoint
crossings is controlled by the lower-density failure probability. -/
theorem bernoulliBondMeasure_real_cubicBox_maxCrossings_le_le
    {d r s : ℕ} {i : Fin d} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {p₁ p₂ : I} (h12 : (p₁ : ℝ) < p₂) :
    (bernoulliBondMeasure d p₂).real
        {ω | maxEdgeDisjointLeftRightCrossings d r i ω ≤ s} ≤
      ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)) ^ s *
        (1 - (bernoulliBondMeasure d p₁).real (cubicBoxCrossingEvent d r i)) := by
  let A : Set (EdgeConfiguration d) :=
    {ω | s + 1 ≤ maxEdgeDisjointLeftRightCrossings d r i ω}
  have hA : A = interiorDepth s (cubicBoxCrossingEvent d r i) := by
    ext ω
    exact (mem_interiorDepth_cubicBoxCrossingEvent_iff_le_max hr ω).symm
  have hAc : Aᶜ = {ω | maxEdgeDisjointLeftRightCrossings d r i ω ≤ s} := by
    ext ω
    simp [A]
  have hAm : MeasurableSet A := by
    rw [hA]
    exact measurableSet_interiorDepth (measurableSet_cubicBoxCrossingEvent d r i) s
  rw [← hAc, measureReal_compl hAm, probReal_univ]
  exact one_sub_bernoulliBondMeasure_real_cubicBox_maxCrossings_ge_le hr hs h12

/-- Equation (7.75), before optimizing the integer crossing threshold.  It combines the
lower-density static-block crossing estimate (7.74) with ACCFR sprinkling and finite edge
Menger. -/
theorem cubicBox_maxCrossings_probability_le_sprinkled_exp_staticTransverse
    {d : ℕ} (hd : 3 ≤ d) (p₁ p₂ q : I) (ε : ℝ)
    (N K s : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K) (hs : 1 ≤ s)
    (h12 : (p₁ : ℝ) < p₂)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p₁ ε N).real
          {η : Set (Cubic d) | cubicOrigin ∈ η}) :
    (bernoulliBondMeasure d p₂).real
        {ω | maxEdgeDisjointLeftRightCrossings d (N * (K + 1))
          (Fin.castLE (by omega) 0) ω ≤ s} ≤
      ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)) ^ s *
        Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ) *
          ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) := by
  have hr : 1 ≤ N * (K + 1) := Nat.mul_pos hN (by omega)
  have hsprinkle := bernoulliBondMeasure_real_cubicBox_maxCrossings_le_le
    (d := d) (r := N * (K + 1)) (s := s)
    (i := Fin.castLE (by omega) 0) hr hs h12
  have hfail := one_sub_cubicBoxCrossing_probability_le_exp_staticTransverse
    hd p₁ q ε N K hN hK hq hqThreshold hmarginal
  have hratio : 0 ≤ (p₂ : ℝ) / ((p₂ : ℝ) - p₁) :=
    div_nonneg p₂.2.1 (sub_nonneg.mpr h12.le)
  exact hsprinkle.trans (mul_le_mul_of_nonneg_left hfail (pow_nonneg hratio s))

/-! ### Comparing the block exponent with the physical surface order -/

theorem div_three_le_staticSeparatedCoordinateCount (K : ℕ) :
    (K : ℝ) / 3 ≤ ((2 * (K / 3) + 1 : ℕ) : ℝ) := by
  have hmod : K % 3 < 3 := Nat.mod_lt K (by omega)
  have hdecomp : K % 3 + 3 * (K / 3) = K := Nat.mod_add_div K 3
  have hnat : K ≤ 3 * (2 * (K / 3) + 1) := by omega
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
  have hcast : (K : ℝ) ≤
      3 * (((2 * (K / 3) + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  simpa [mul_comm] using hcast

/-- The number of independent transverse slices times their planar length has the expected
surface-order lower bound. -/
theorem staticTransverseScale_ge_radiusPower
    {d K : ℕ} (hd : 3 ≤ d) :
    (K : ℝ) * ((2 * (K / 3) + 1) ^ (d - 2) : ℕ) ≥
      (K : ℝ) ^ (d - 1) / 3 ^ (d - 2) := by
  have hbase := div_three_le_staticSeparatedCoordinateCount K
  have hpow : ((K : ℝ) / 3) ^ (d - 2) ≤
      (((2 * (K / 3) + 1 : ℕ) : ℝ)) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) hbase (d - 2)
  have hmul := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg K)
  have hdEq : d - 1 = (d - 2) + 1 := by omega
  calc
    (K : ℝ) ^ (d - 1) / 3 ^ (d - 2) =
        (K : ℝ) * ((K : ℝ) / 3) ^ (d - 2) := by
      rw [hdEq, pow_succ, div_pow]
      ring
    _ ≤ (K : ℝ) * (((2 * (K / 3) + 1 : ℕ) : ℝ)) ^ (d - 2) := hmul
    _ = (K : ℝ) * ((2 * (K / 3) + 1) ^ (d - 2) : ℕ) := by
      norm_cast

theorem scaledStaticBoxRadius_pow_le
    {d N K : ℕ} (hK : 1 ≤ K) :
    ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) ≤
      (((2 * N : ℕ) : ℝ) ^ (d - 1)) * (K : ℝ) ^ (d - 1) := by
  have hnat : N * (K + 1) ≤ (2 * N) * K := by
    nlinarith
  have hbase : ((N * (K + 1) : ℕ) : ℝ) ≤
      (((2 * N : ℕ) : ℝ) * (K : ℝ)) := by
    exact_mod_cast hnat
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (N * (K + 1))) hbase (d - 1)
  simpa [mul_pow] using hp

/-- Uniform comparison used to rewrite the exponential slice bound in terms of the physical
box radius `N(K+1)`. -/
theorem scaledStaticBoxRadius_pow_le_constant_mul_staticTransverseScale
    {d N K : ℕ} (hd : 3 ≤ d) (hK : 1 ≤ K) :
    ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) ≤
      (3 : ℝ) ^ (d - 2) * (((2 * N : ℕ) : ℝ) ^ (d - 1)) *
        ((K : ℝ) * ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) := by
  have hscaled := scaledStaticBoxRadius_pow_le (d := d) (N := N) hK
  have htrans := staticTransverseScale_ge_radiusPower (d := d) (K := K) hd
  have hthree : (0 : ℝ) < 3 ^ (d - 2) := by positivity
  have hkpow : (K : ℝ) ^ (d - 1) ≤
      3 ^ (d - 2) *
        ((K : ℝ) * ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ hthree).mp htrans
  calc
    ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) ≤
        (((2 * N : ℕ) : ℝ) ^ (d - 1)) * (K : ℝ) ^ (d - 1) := hscaled
    _ ≤ (((2 * N : ℕ) : ℝ) ^ (d - 1)) *
        (3 ^ (d - 2) *
          ((K : ℝ) * ((2 * (K / 3) + 1) ^ (d - 2) : ℕ))) :=
      mul_le_mul_of_nonneg_left hkpow (by positivity)
    _ = (3 : ℝ) ^ (d - 2) * (((2 * N : ℕ) : ℝ) ^ (d - 1)) *
        ((K : ℝ) * ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) := by ring

/-! ### Optimizing the integer crossing threshold -/

/-- The elementary optimization behind the passage from (7.75) to a surface-order
exponential estimate.  The factor `4` leaves enough room both for the integer floor and for
halving the lower-density exponential rate. -/
theorem pow_mul_exp_neg_le_exp_neg_half_of_cast_le
    {A a b c x : ℝ} {s : ℕ}
    (hA : 1 < A) (hc : 0 < c) (hx : 0 ≤ x)
    (hs : (s : ℝ) ≤ c / (4 * Real.log A) * x)
    (hdecay : c * x ≤ a * b) :
    A ^ s * Real.exp (-a * b) ≤ Real.exp (-(c / 2) * x) := by
  have hApos : 0 < A := zero_lt_one.trans hA
  have hlog : 0 < Real.log A := Real.log_pos hA
  have hthresholdLog :
      (c / (4 * Real.log A) * x) * Real.log A = c * x / 4 := by
    field_simp [hlog.ne']
    <;> ring
  have hslog : (s : ℝ) * Real.log A ≤ c * x / 4 := by
    calc
      (s : ℝ) * Real.log A ≤
          (c / (4 * Real.log A) * x) * Real.log A :=
        mul_le_mul_of_nonneg_right hs hlog.le
      _ = c * x / 4 := hthresholdLog
  have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
  have hexponent : (s : ℝ) * Real.log A + (-a * b) ≤ -(c / 2) * x := by
    linarith
  have hpow : A ^ s = Real.exp ((s : ℝ) * Real.log A) := by
    calc
      A ^ s = (Real.exp (Real.log A)) ^ s := by rw [Real.exp_log hApos]
      _ = Real.exp ((s : ℝ) * Real.log A) :=
        (Real.exp_nat_mul (Real.log A) s).symm
  rw [hpow, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexponent

/-- The dimension/block-size comparison denominator in the surface-order estimate. -/
noncomputable def staticManyCrossingsComparisonDenominator (d N : ℕ) : ℝ :=
  (3 : ℝ) ^ (d - 2) * (((2 * N : ℕ) : ℝ) ^ (d - 1))

/-- The lower-density exponential rate after conversion from the slice scale to the physical
surface scale. -/
noncomputable def staticManyCrossingsComparisonRate (d N : ℕ) : ℝ :=
  siteSquareCrossingPeierlsRate / staticManyCrossingsComparisonDenominator d N

/-- The density of disjoint crossings retained after sprinkling from `p₁` to `p₂`. -/
noncomputable def staticManyCrossingsDensity (d N : ℕ) (p₁ p₂ : I) : ℝ :=
  staticManyCrossingsComparisonRate d N /
    (4 * Real.log ((p₂ : ℝ) / ((p₂ : ℝ) - p₁)))

/-- Half the comparison rate, used as the final surface-order exponential rate. -/
noncomputable def staticManyCrossingsExponentialRate (d N : ℕ) : ℝ :=
  staticManyCrossingsComparisonRate d N / 2

theorem staticManyCrossingsComparisonDenominator_pos
    {d N : ℕ} (hN : 1 ≤ N) :
    0 < staticManyCrossingsComparisonDenominator d N := by
  simp only [staticManyCrossingsComparisonDenominator]
  positivity

theorem staticManyCrossingsComparisonRate_pos
    {d N : ℕ} (hN : 1 ≤ N) :
    0 < staticManyCrossingsComparisonRate d N := by
  exact div_pos siteSquareCrossingPeierlsRate_pos
    (staticManyCrossingsComparisonDenominator_pos hN)

theorem staticManyCrossings_sprinklingRatio_one_lt
    {p₁ p₂ : I} (hp₁ : 0 < (p₁ : ℝ)) (h12 : (p₁ : ℝ) < p₂) :
    1 < (p₂ : ℝ) / ((p₂ : ℝ) - p₁) := by
  have hden : 0 < (p₂ : ℝ) - p₁ := sub_pos.mpr h12
  apply (one_lt_div hden).2
  linarith

theorem staticManyCrossingsDensity_pos
    {d N : ℕ} (hN : 1 ≤ N) {p₁ p₂ : I}
    (hp₁ : 0 < (p₁ : ℝ)) (h12 : (p₁ : ℝ) < p₂) :
    0 < staticManyCrossingsDensity d N p₁ p₂ := by
  exact div_pos (staticManyCrossingsComparisonRate_pos hN)
    (mul_pos (by norm_num)
      (Real.log_pos (staticManyCrossings_sprinklingRatio_one_lt hp₁ h12)))

theorem staticManyCrossingsExponentialRate_pos
    {d N : ℕ} (hN : 1 ≤ N) :
    0 < staticManyCrossingsExponentialRate d N := by
  exact div_pos (staticManyCrossingsComparisonRate_pos hN) (by norm_num)

/-- A cofinal block-scale threshold beyond which the integer crossing count chosen by the
sprinkling optimization is nonzero. -/
noncomputable def staticManyCrossingsBlockThreshold
    (d N : ℕ) (p₁ p₂ : I) : ℕ :=
  max 1 ⌈1 / staticManyCrossingsDensity d N p₁ p₂⌉₊

theorem staticManyCrossingsBlockThreshold_pos
    {d N : ℕ} {p₁ p₂ : I} :
    1 ≤ staticManyCrossingsBlockThreshold d N p₁ p₂ := by
  exact le_max_left _ _

/-- The physical surface order of an aligned box dominates the coarse block scale. -/
theorem blockScale_le_scaledStaticBoxRadius_pow
    {d N K : ℕ} (hd : 3 ≤ d) (hN : 1 ≤ N) :
    (K : ℝ) ≤ ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) := by
  have hbaseNat : K ≤ N * (K + 1) := by nlinarith
  have hbase : (K : ℝ) ≤ ((N * (K + 1) : ℕ) : ℝ) := by
    exact_mod_cast hbaseNat
  have hrOne : (1 : ℝ) ≤ ((N * (K + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hN (by omega : 0 < K + 1))
  calc
    (K : ℝ) ≤ ((N * (K + 1) : ℕ) : ℝ) := hbase
    _ = ((N * (K + 1) : ℕ) : ℝ) ^ 1 := by ring
    _ ≤ ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) :=
      pow_le_pow_right₀ hrOne (by omega)

theorem one_le_staticManyCrossingsDensity_mul_surface_of_threshold_le
    {d N K : ℕ} (hd : 3 ≤ d) (hN : 1 ≤ N)
    {p₁ p₂ : I} (hp₁ : 0 < (p₁ : ℝ)) (h12 : (p₁ : ℝ) < p₂)
    (hK : staticManyCrossingsBlockThreshold d N p₁ p₂ ≤ K) :
    1 ≤ staticManyCrossingsDensity d N p₁ p₂ *
      ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) := by
  let β := staticManyCrossingsDensity d N p₁ p₂
  have hβ : 0 < β := staticManyCrossingsDensity_pos hN hp₁ h12
  have hceilNat : ⌈1 / β⌉₊ ≤ K :=
    (le_max_right 1 ⌈1 / β⌉₊).trans hK
  have hceil : (1 / β : ℝ) ≤ (K : ℝ) := by
    exact (Nat.le_ceil (1 / β)).trans (by exact_mod_cast hceilNat)
  have hsurface := blockScale_le_scaledStaticBoxRadius_pow (d := d) (K := K) hd hN
  calc
    (1 : ℝ) = β * (1 / β) := by field_simp [hβ.ne']
    _ ≤ β * (K : ℝ) := mul_le_mul_of_nonneg_left hceil hβ.le
    _ ≤ β * ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) :=
      mul_le_mul_of_nonneg_left hsurface hβ.le
    _ = staticManyCrossingsDensity d N p₁ p₂ *
        ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) := rfl

/-- The optimized aligned-box form of (7.75).  The hypothesis `hlarge` is precisely the
non-vacuity condition for the integer threshold; a later cofinality lemma removes it for all
sufficiently large aligned radii. -/
theorem cubicBox_maxCrossings_probability_le_exp_surface
    {d : ℕ} (hd : 3 ≤ d) (p₁ p₂ q : I) (ε : ℝ)
    (N K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K)
    (hp₁ : 0 < (p₁ : ℝ)) (h12 : (p₁ : ℝ) < p₂)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p₁ ε N).real
          {η : Set (Cubic d) | cubicOrigin ∈ η})
    (hlarge :
      1 ≤ staticManyCrossingsDensity d N p₁ p₂ *
        ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)) :
    (bernoulliBondMeasure d p₂).real
        {ω | maxEdgeDisjointLeftRightCrossings d (N * (K + 1))
          (Fin.castLE (by omega) 0) ω ≤
            ⌊staticManyCrossingsDensity d N p₁ p₂ *
              ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)⌋₊} ≤
      Real.exp (-staticManyCrossingsExponentialRate d N *
        ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)) := by
  let X : ℝ := ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)
  let B : ℝ := (K : ℝ) * ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)
  let A : ℝ := (p₂ : ℝ) / ((p₂ : ℝ) - p₁)
  let c : ℝ := staticManyCrossingsComparisonRate d N
  let s : ℕ := ⌊staticManyCrossingsDensity d N p₁ p₂ * X⌋₊
  have hA : 1 < A := staticManyCrossings_sprinklingRatio_one_lt hp₁ h12
  have hc : 0 < c := staticManyCrossingsComparisonRate_pos hN
  have hX : 0 ≤ X := by positivity
  have hs : 1 ≤ s := by
    rw [show s = ⌊staticManyCrossingsDensity d N p₁ p₂ * X⌋₊ by rfl,
      Nat.one_le_floor_iff]
    simpa [X] using hlarge
  have hsCast : (s : ℝ) ≤ c / (4 * Real.log A) * X := by
    have hfloor : (s : ℝ) ≤ staticManyCrossingsDensity d N p₁ p₂ * X := by
      apply Nat.floor_le
      positivity
    simpa [staticManyCrossingsDensity, c, A] using hfloor
  have hsurface :=
    scaledStaticBoxRadius_pow_le_constant_mul_staticTransverseScale
      (d := d) (N := N) (K := K) hd hK
  have hD : 0 < staticManyCrossingsComparisonDenominator d N :=
    staticManyCrossingsComparisonDenominator_pos hN
  have hXB : X / staticManyCrossingsComparisonDenominator d N ≤ B := by
    apply (div_le_iff₀ hD).2
    simpa [X, B, staticManyCrossingsComparisonDenominator, mul_comm, mul_left_comm,
      mul_assoc] using hsurface
  have hdecay : c * X ≤ siteSquareCrossingPeierlsRate * B := by
    calc
      c * X = siteSquareCrossingPeierlsRate *
          (X / staticManyCrossingsComparisonDenominator d N) := by
        simp only [c, staticManyCrossingsComparisonRate]
        field_simp [hD.ne']
        <;> ring
      _ ≤ siteSquareCrossingPeierlsRate * B :=
        mul_le_mul_of_nonneg_left hXB siteSquareCrossingPeierlsRate_pos.le
  have hraw := cubicBox_maxCrossings_probability_le_sprinkled_exp_staticTransverse
    hd p₁ p₂ q ε N K s hN hK hs h12 hq hqThreshold hmarginal
  refine hraw.trans ?_
  have hoptimized :=
    pow_mul_exp_neg_le_exp_neg_half_of_cast_le hA hc hX hsCast hdecay
  change A ^ s * Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ) *
      ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) ≤
    Real.exp (-(c / 2) * X)
  calc
    A ^ s * Real.exp (-siteSquareCrossingPeierlsRate * (K : ℝ) *
        ((2 * (K / 3) + 1) ^ (d - 2) : ℕ)) =
        A ^ s * Real.exp (-siteSquareCrossingPeierlsRate * B) := by
      congr 2
      dsimp [B]
      ring
    _ ≤ Real.exp (-(c / 2) * X) := hoptimized

/-- Cofinal aligned-radius form of the surface-order many-crossings estimate. -/
theorem cubicBox_maxCrossings_probability_le_exp_surface_of_threshold_le
    {d : ℕ} (hd : 3 ≤ d) (p₁ p₂ q : I) (ε : ℝ)
    (N K : ℕ) (hN : 1 ≤ N)
    (hp₁ : 0 < (p₁ : ℝ)) (h12 : (p₁ : ℝ) < p₂)
    (hK : staticManyCrossingsBlockThreshold d N p₁ p₂ ≤ K)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p₁ ε N).real
          {η : Set (Cubic d) | cubicOrigin ∈ η}) :
    (bernoulliBondMeasure d p₂).real
        {ω | maxEdgeDisjointLeftRightCrossings d (N * (K + 1))
          (Fin.castLE (by omega) 0) ω ≤
            ⌊staticManyCrossingsDensity d N p₁ p₂ *
              ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)⌋₊} ≤
      Real.exp (-staticManyCrossingsExponentialRate d N *
        ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)) := by
  have hKone : 1 ≤ K :=
    staticManyCrossingsBlockThreshold_pos.trans hK
  exact cubicBox_maxCrossings_probability_le_exp_surface
    hd p₁ p₂ q ε N K hN hKone hp₁ h12 hq hqThreshold hmarginal
    (one_le_staticManyCrossingsDensity_mul_surface_of_threshold_le
      hd hN hp₁ h12 hK)

/-- Source-facing aligned-radius form of Theorem 7.68.  The crossing count is coerced to
`ℝ`, so the statement contains exactly the source threshold `β r^(d-1)` and no undocumented
floor convention. -/
theorem maxEdgeDisjointCrossings_probability_ge_aligned
    {d : ℕ} (hd : 3 ≤ d) (p₁ p₂ q : I) (ε : ℝ)
    (N K : ℕ) (hN : 1 ≤ N)
    (hp₁ : 0 < (p₁ : ℝ)) (h12 : (p₁ : ℝ) < p₂)
    (hK : staticManyCrossingsBlockThreshold d N p₁ p₂ ≤ K)
    (hq : (q : ℝ) < 1)
    (hqThreshold : siteSquareCrossingPeierlsThreshold < (q : ℝ))
    (hmarginal :
      (lssMarginalThresholdUnit
          (3 ^ d * (3 * d + 1) ^ d) q hq : ℝ) ≤
        (epsilonGoodBlockLaw d p₁ ε N).real
          {η : Set (Cubic d) | cubicOrigin ∈ η}) :
    1 - Real.exp (-staticManyCrossingsExponentialRate d N *
        ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)) ≤
      (bernoulliBondMeasure d p₂).real
        {ω | staticManyCrossingsDensity d N p₁ p₂ *
            ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1) ≤
          (maxEdgeDisjointLeftRightCrossings d (N * (K + 1))
            (Fin.castLE (by omega) 0) ω : ℝ)} := by
  let r := N * (K + 1)
  let i : Fin d := Fin.castLE (by omega) 0
  let t := staticManyCrossingsDensity d N p₁ p₂ *
    ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)
  let G : Set (EdgeConfiguration d) :=
    {ω | t ≤ (maxEdgeDisjointLeftRightCrossings d r i ω : ℝ)}
  let F : Set (EdgeConfiguration d) :=
    {ω | maxEdgeDisjointLeftRightCrossings d r i ω ≤ ⌊t⌋₊}
  have hr : 1 ≤ r := by
    exact Nat.mul_pos hN (by omega)
  have hGF : Gᶜ ⊆ F := by
    intro ω hω
    have hlt : (maxEdgeDisjointLeftRightCrossings d r i ω : ℝ) < t := by
      simpa only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hω
    exact Nat.le_floor hlt.le
  have hF := cubicBox_maxCrossings_probability_le_exp_surface_of_threshold_le
    hd p₁ p₂ q ε N K hN hp₁ h12 hK hq hqThreshold hmarginal
  have hbad : (bernoulliBondMeasure d p₂).real Gᶜ ≤
      Real.exp (-staticManyCrossingsExponentialRate d N *
        ((N * (K + 1) : ℕ) : ℝ) ^ (d - 1)) := by
    exact (measureReal_mono hGF).trans (by simpa [F, r, i, t] using hF)
  have hGm : MeasurableSet G := by
    exact measurableSet_cast_maxEdgeDisjointLeftRightCrossings_ge hr t
  rw [measureReal_compl hGm, probReal_univ] at hbad
  simpa [G, r, i, t, add_comm] using hbad

end Percolation
