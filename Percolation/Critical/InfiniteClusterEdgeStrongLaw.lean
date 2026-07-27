import Percolation.Critical.InfiniteClusterEdgeDensity
import Percolation.Critical.FiniteCylinderStrongLaw
import Percolation.Critical.SupercriticalRadiusPositivity

/-!
# Finite-radius approximation of infinite-cluster edge densities

For a fixed positively oriented edge at the origin, replace "touches an infinite cluster" by
"one endpoint reaches its coordinate-box surface at radius `r`". These events have support of
radius at most `r+1`; their error is covered by two translated finite-cluster radius events.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators symmDiff unitInterval

/-- The positively oriented reference edge in coordinate direction `i`. -/
def positiveCoordinateEdge (d : ℕ) (i : Fin d) : CubicEdge d :=
  cubicStepEdge cubicOrigin (i, true)

@[simp]
theorem cubicTranslationIso_mapEdgeSet_positiveCoordinateEdge
    {d : ℕ} (i : Fin d) (x : Cubic d) :
    (cubicTranslationIso cubicOrigin x).mapEdgeSet (positiveCoordinateEdge d i) =
      cubicStepEdge x (i, true) := by
  apply Subtype.ext
  change Sym2.map (cubicTranslate cubicOrigin x)
      s(cubicOrigin, cubicStepFrom cubicOrigin (i, true)) =
    s(x, cubicStepFrom x (i, true))
  rw [Sym2.map_mk, cubicTranslate_self,
    cubicTranslate_stepFrom_right, cubicTranslate_self]

/-- Translating the reference interior-edge event places it at the positively oriented edge
based at `x`. -/
theorem translatedCylinderEvent_infiniteClusterInteriorPositiveEdge
    {d : ℕ} (i : Fin d) (x : Cubic d) :
    translatedCylinderEvent x
        (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i)) =
      infiniteClusterInteriorEdgeEvent (cubicStepEdge x (i, true)) := by
  ext omega
  change cubicTranslationConfigurationPullback cubicOrigin x omega ∈
      infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i) ↔ _
  rw [mem_infiniteClusterInteriorEdgeEvent_iff,
    mem_infiniteClusterInteriorEdgeEvent_iff]
  let F := cubicTranslationIso cubicOrigin x
  have hmap : F.mapEdgeSet (positiveCoordinateEdge d i) =
      cubicStepEdge x (i, true) :=
    cubicTranslationIso_mapEdgeSet_positiveCoordinateEdge i x
  constructor
  · rintro ⟨heOpen, y, hye, hyInf⟩
    refine ⟨?_, cubicTranslate cubicOrigin x y, ?_, ?_⟩
    · change F.mapEdgeSet (positiveCoordinateEdge d i) ∈ omega at heOpen
      simpa only [hmap] using heOpen
    · have hyMap : cubicTranslate cubicOrigin x y ∈
          (F.mapEdgeSet (positiveCoordinateEdge d i) : Sym2 (Cubic d)) := by
        rw [SimpleGraph.Iso.mapEdgeSet_apply]
        exact Sym2.mem_map.mpr ⟨y,
          (by simpa only [Sym2.mem_toFinset] using hye), rfl⟩
      simpa only [hmap, Sym2.mem_toFinset] using hyMap
    · exact (cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff
        omega cubicOrigin x y).mp hyInf
  · rintro ⟨heOpen, z, hze, hzInf⟩
    have hzMap : z ∈
        (F.mapEdgeSet (positiveCoordinateEdge d i) : Sym2 (Cubic d)) := by
      simpa only [hmap, Sym2.mem_toFinset] using hze
    rw [SimpleGraph.Iso.mapEdgeSet_apply] at hzMap
    change z ∈ Sym2.map F (positiveCoordinateEdge d i).1 at hzMap
    obtain ⟨y, hye, rfl⟩ := Sym2.mem_map.mp hzMap
    refine ⟨?_, y, (by simpa only [Sym2.mem_toFinset] using hye), ?_⟩
    · change F.mapEdgeSet (positiveCoordinateEdge d i) ∈ omega
      simpa only [hmap] using heOpen
    · exact (cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff
        omega cubicOrigin x y).mpr hzInf

/-- Translating the reference boundary-edge event places it at the positively oriented edge
based at `x`. -/
theorem translatedCylinderEvent_infiniteClusterBoundaryPositiveEdge
    {d : ℕ} (i : Fin d) (x : Cubic d) :
    translatedCylinderEvent x
        (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i)) =
      infiniteClusterBoundaryEdgeEvent (cubicStepEdge x (i, true)) := by
  ext omega
  change cubicTranslationConfigurationPullback cubicOrigin x omega ∈
      infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i) ↔ _
  rw [mem_infiniteClusterBoundaryEdgeEvent_iff,
    mem_infiniteClusterBoundaryEdgeEvent_iff]
  let F := cubicTranslationIso cubicOrigin x
  have hmap : F.mapEdgeSet (positiveCoordinateEdge d i) =
      cubicStepEdge x (i, true) :=
    cubicTranslationIso_mapEdgeSet_positiveCoordinateEdge i x
  constructor
  · rintro ⟨heClosed, y, hye, hyInf⟩
    refine ⟨?_, cubicTranslate cubicOrigin x y, ?_, ?_⟩
    · intro heOpen
      apply heClosed
      change F.mapEdgeSet (positiveCoordinateEdge d i) ∈ omega
      simpa only [hmap] using heOpen
    · have hyMap : cubicTranslate cubicOrigin x y ∈
          (F.mapEdgeSet (positiveCoordinateEdge d i) : Sym2 (Cubic d)) := by
        rw [SimpleGraph.Iso.mapEdgeSet_apply]
        exact Sym2.mem_map.mpr ⟨y,
          (by simpa only [Sym2.mem_toFinset] using hye), rfl⟩
      simpa only [hmap, Sym2.mem_toFinset] using hyMap
    · exact (cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff
        omega cubicOrigin x y).mp hyInf
  · rintro ⟨heClosed, z, hze, hzInf⟩
    have hzMap : z ∈
        (F.mapEdgeSet (positiveCoordinateEdge d i) : Sym2 (Cubic d)) := by
      simpa only [hmap, Sym2.mem_toFinset] using hze
    rw [SimpleGraph.Iso.mapEdgeSet_apply] at hzMap
    change z ∈ Sym2.map F (positiveCoordinateEdge d i).1 at hzMap
    obtain ⟨y, hye, rfl⟩ := Sym2.mem_map.mp hzMap
    refine ⟨?_, y, (by simpa only [Sym2.mem_toFinset] using hye), ?_⟩
    · intro heOpen
      apply heClosed
      change F.mapEdgeSet (positiveCoordinateEdge d i) ∈ omega at heOpen
      simpa only [hmap] using heOpen
    · exact (cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff
        omega cubicOrigin x y).mpr hzInf

@[simp]
theorem cubicStepEdge_negative_eq_positiveFromNeighbor
    {d : ℕ} (x : Cubic d) (i : Fin d) :
    cubicStepEdge x (i, false) =
      cubicStepEdge (cubicStepFrom x (i, false)) (i, true) := by
  apply Subtype.ext
  simp only [cubicStepEdge, cubicStepFrom_neg_pos]
  exact Sym2.eq_swap

private theorem cubicStepFrom_pos_pos_ne
    {d : ℕ} (x : Cubic d) (i j : Fin d) :
    cubicStepFrom (cubicStepFrom x (i, true)) (j, true) ≠ x := by
  intro h
  have hi := congrFun h i
  by_cases hij : i = j
  · subst j
    simp [cubicStepFrom, cubicDirectionIncrement] at hi
    omega
  · simp [cubicStepFrom, cubicDirectionIncrement, hij] at hi

/-- A cubic edge has a unique representation by its lower endpoint and a positive coordinate
direction. -/
theorem positiveCubicStepEdge_injective {d : ℕ} :
    Function.Injective
      (fun xi : Cubic d × Fin d ↦ cubicStepEdge xi.1 (xi.2, true)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have hs : s(x, cubicStepFrom x (i, true)) =
      s(y, cubicStepFrom y (j, true)) := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp hs with halign | hswap
  · have hxy : x = y := halign.1
    subst y
    have hij : i = j := by
      exact congrArg Prod.fst (cubicStepFrom_injective x halign.2)
    subst j
    rfl
  · exfalso
    apply cubicStepFrom_pos_pos_ne y j i
    rw [← hswap.1, hswap.2]

/-- Embedding which enumerates every unoriented cubic edge exactly once using positive
directions. -/
def positiveCubicEdgeEmbedding (d : ℕ) : Cubic d × Fin d ↪ CubicEdge d where
  toFun xi := cubicStepEdge xi.1 (xi.2, true)
  inj' := positiveCubicStepEdge_injective

/-- Positive-direction representatives whose two endpoints lie in the centered box. -/
noncomputable def positiveInternalBoxEdgePairs (d n : ℕ) :
    Finset (Cubic d × Fin d) := by
  classical
  exact ((cubicMetricBox d cubicOrigin n).product Finset.univ).filter fun xi ↦
    cubicStepFrom xi.1 (xi.2, true) ∈ cubicMetricBox d cubicOrigin n

/-- The positive-direction representatives as a finset of unoriented edges. -/
noncomputable def positiveInternalBoxEdges (d n : ℕ) : Finset (CubicEdge d) :=
  (positiveInternalBoxEdgePairs d n).map (positiveCubicEdgeEmbedding d)

/-- All positively oriented edges based in the box, including the outward edges based on its
positive faces. -/
noncomputable def positiveBoxEdgePairs (d n : ℕ) : Finset (Cubic d × Fin d) :=
  (cubicMetricBox d cubicOrigin n).product Finset.univ

/-- Outward positive representatives: their base lies in the box and their other endpoint does
not. -/
noncomputable def positiveOuterBoxEdgePairs (d n : ℕ) : Finset (Cubic d × Fin d) :=
  (positiveBoxEdgePairs d n).filter fun xi ↦
    cubicStepFrom xi.1 (xi.2, true) ∉ cubicMetricBox d cubicOrigin n

theorem positiveInternalBoxEdges_eq_cubicBoxEdges (d n : ℕ) :
    positiveInternalBoxEdges d n = cubicBoxEdges d cubicOrigin n := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨xi, hxi, hmap⟩ := Finset.mem_map.mp he
    rw [positiveInternalBoxEdgePairs, Finset.mem_filter] at hxi
    have hx := (Finset.mem_product.mp hxi.1).1
    rw [← hmap]
    exact cubicStepEdge_mem_cubicBoxEdges hx hxi.2
  · intro he
    simp only [cubicBoxEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨x, hx, a, hxa, rfl⟩ := he
    rcases a with ⟨i, b⟩
    cases b
    · apply Finset.mem_map.mpr
      refine ⟨(cubicStepFrom x (i, false), i), ?_, ?_⟩
      · rw [positiveInternalBoxEdgePairs, Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hxa, Finset.mem_univ i⟩,
          by simpa only [cubicStepFrom_neg_pos] using hx⟩
      · exact (cubicStepEdge_negative_eq_positiveFromNeighbor x i).symm
    · apply Finset.mem_map.mpr
      refine ⟨(x, i), ?_, rfl⟩
      rw [positiveInternalBoxEdgePairs, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_univ i⟩, hxa⟩

theorem positiveInternalBoxEdgePairs_subset_positiveBoxEdgePairs (d n : ℕ) :
    positiveInternalBoxEdgePairs d n ⊆ positiveBoxEdgePairs d n := by
  intro xi hxi
  rw [positiveInternalBoxEdgePairs, Finset.mem_filter] at hxi
  simpa only [positiveBoxEdgePairs] using hxi.1

theorem positiveBoxEdgePairs_subset_internal_union_outer (d n : ℕ) :
    positiveBoxEdgePairs d n ⊆
      positiveInternalBoxEdgePairs d n ∪ positiveOuterBoxEdgePairs d n := by
  intro xi hxi
  by_cases hstep : cubicStepFrom xi.1 (xi.2, true) ∈
      cubicMetricBox d cubicOrigin n
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hxi, hstep⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hxi, hstep⟩

private theorem base_mem_boxSurface_of_positiveStep_not_mem_box
    {d n : ℕ} {x : Cubic d} {i : Fin d}
    (hx : x ∈ cubicMetricBox d cubicOrigin n)
    (hstep : cubicStepFrom x (i, true) ∉ cubicMetricBox d cubicOrigin n) :
    x ∈ cubicBoxSurface d cubicOrigin n := by
  have hxi := mem_cubicMetricBox.mp hx i
  simp only [cubicOrigin] at hxi
  have hcoord : x i = (n : ℤ) := by
    by_contra hne
    have hxi' : x i ≤ (n : ℤ) := by simpa using hxi.2
    have hxilow : -(n : ℤ) ≤ x i := by simpa using hxi.1
    have hlt : x i < (n : ℤ) := lt_of_le_of_ne hxi' hne
    apply hstep
    rw [mem_cubicMetricBox]
    intro j
    have hxj := mem_cubicMetricBox.mp hx j
    simp only [cubicOrigin] at hxj
    by_cases hji : j = i
    · subst j
      simpa [cubicOrigin, cubicStepFrom, cubicDirectionIncrement] using
        (show -(n : ℤ) ≤ x i + 1 ∧ x i + 1 ≤ (n : ℤ) by
          constructor <;> omega)
    · simp only [cubicOrigin, cubicStepFrom, cubicDirectionIncrement,
        Function.update_of_ne hji]
      exact hxj
  rw [mem_cubicBoxSurface]
  apply le_antisymm (mem_cubicMetricBox_iff_lInfDist_le.mp hx)
  have hi := cubicLInfDist_coord_le cubicOrigin x i
  simpa [cubicOrigin, hcoord] using hi

theorem positiveOuterBoxEdgePairs_subset_surface_product (d n : ℕ) :
    positiveOuterBoxEdgePairs d n ⊆
      (cubicBoxSurface d cubicOrigin n).product Finset.univ := by
  rintro ⟨x, i⟩ hxi
  rw [positiveOuterBoxEdgePairs, Finset.mem_filter] at hxi
  have hx := (Finset.mem_product.mp hxi.1).1
  exact Finset.mem_product.mpr
    ⟨base_mem_boxSurface_of_positiveStep_not_mem_box hx hxi.2,
      Finset.mem_univ i⟩

theorem positiveOuterBoxEdgePairs_card_le (d n : ℕ) :
    (positiveOuterBoxEdgePairs d n).card ≤
      (cubicBoxSurface d cubicOrigin n).card * d := by
  calc
    (positiveOuterBoxEdgePairs d n).card ≤
        ((cubicBoxSurface d cubicOrigin n).product Finset.univ).card :=
      Finset.card_le_card (positiveOuterBoxEdgePairs_subset_surface_product d n)
    _ = (cubicBoxSurface d cubicOrigin n).card * d := by simp

/-- Sum of the `d` positively oriented interior-edge fields over a finite vertex set.  The
normalization is per vertex, so each unoriented lattice edge is represented once away from the
boundary of the averaging set. -/
noncomputable def positiveInfiniteClusterInteriorEdgeAverage
    (d : ℕ) (s : Finset (Cubic d)) (omega : EdgeConfiguration d) : ℝ :=
  ∑ i : Fin d, translatedEventAverage
    (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i)) s omega

/-- Positively oriented boundary-edge analogue of
`positiveInfiniteClusterInteriorEdgeAverage`. -/
noncomputable def positiveInfiniteClusterBoundaryEdgeAverage
    (d : ℕ) (s : Finset (Cubic d)) (omega : EdgeConfiguration d) : ℝ :=
  ∑ i : Fin d, translatedEventAverage
    (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i)) s omega

theorem translatedInfiniteClusterInteriorPositiveEdgeAverage_eq
    {d : ℕ} (i : Fin d) (s : Finset (Cubic d)) (omega : EdgeConfiguration d) :
    translatedEventAverage
        (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i)) s omega =
      (∑ x ∈ s,
        eventIndicator
          (infiniteClusterInteriorEdgeEvent (cubicStepEdge x (i, true))) omega) /
        (s.card : ℝ) := by
  unfold translatedEventAverage translatedCylinderIndicator
  simp_rw [translatedCylinderEvent_infiniteClusterInteriorPositiveEdge]

theorem translatedInfiniteClusterBoundaryPositiveEdgeAverage_eq
    {d : ℕ} (i : Fin d) (s : Finset (Cubic d)) (omega : EdgeConfiguration d) :
    translatedEventAverage
        (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i)) s omega =
      (∑ x ∈ s,
        eventIndicator
          (infiniteClusterBoundaryEdgeEvent (cubicStepEdge x (i, true))) omega) /
        (s.card : ℝ) := by
  unfold translatedEventAverage translatedCylinderIndicator
  simp_rw [translatedCylinderEvent_infiniteClusterBoundaryPositiveEdge]

/-- Count of all positively oriented interior edges based in the box, including the possible
outward edges based on the positive faces. -/
noncomputable def positiveBoxInteriorEdgeCount (d n : ℕ)
    (omega : EdgeConfiguration d) : ℕ := by
  classical
  exact ((positiveBoxEdgePairs d n).filter fun xi ↦
    omega ∈ infiniteClusterInteriorEdgeEvent
      (cubicStepEdge xi.1 (xi.2, true))).card

/-- Count of all positively oriented boundary edges based in the box. -/
noncomputable def positiveBoxBoundaryEdgeCount (d n : ℕ)
    (omega : EdgeConfiguration d) : ℕ := by
  classical
  exact ((positiveBoxEdgePairs d n).filter fun xi ↦
    omega ∈ infiniteClusterBoundaryEdgeEvent
      (cubicStepEdge xi.1 (xi.2, true))).card

noncomputable def positiveInternalBoxInteriorEdgeCount (d n : ℕ)
    (omega : EdgeConfiguration d) : ℕ := by
  classical
  exact ((positiveInternalBoxEdgePairs d n).filter fun xi ↦
    omega ∈ infiniteClusterInteriorEdgeEvent
      (cubicStepEdge xi.1 (xi.2, true))).card

noncomputable def positiveInternalBoxBoundaryEdgeCount (d n : ℕ)
    (omega : EdgeConfiguration d) : ℕ := by
  classical
  exact ((positiveInternalBoxEdgePairs d n).filter fun xi ↦
    omega ∈ infiniteClusterBoundaryEdgeEvent
      (cubicStepEdge xi.1 (xi.2, true))).card

private theorem cast_card_filter_eq_sum_eventIndicator
    {α Ω : Type*} (s : Finset α) (A : α → Set Ω) (omega : Ω)
    [DecidablePred fun x ↦ omega ∈ A x] :
    (((s.filter fun x ↦ omega ∈ A x).card : ℕ) : ℝ) =
      ∑ x ∈ s, eventIndicator (A x) omega := by
  classical
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : omega ∈ A x <;> simp [eventIndicator, h]

theorem infiniteClusterInteriorEdgeCount_eq_positiveInternalPairs
    (d n : ℕ) (omega : EdgeConfiguration d) :
    infiniteClusterInteriorEdgeCount d n omega =
      positiveInternalBoxInteriorEdgeCount d n omega := by
  classical
  unfold infiniteClusterInteriorEdgeCount
  rw [← positiveInternalBoxEdges_eq_cubicBoxEdges]
  simp only [positiveInternalBoxEdges, Finset.filter_map, Finset.card_map]
  rfl

theorem infiniteClusterBoundaryEdgeCount_eq_positiveInternalPairs
    (d n : ℕ) (omega : EdgeConfiguration d) :
    infiniteClusterBoundaryEdgeCount d n omega =
      positiveInternalBoxBoundaryEdgeCount d n omega := by
  classical
  unfold infiniteClusterBoundaryEdgeCount
  rw [← positiveInternalBoxEdges_eq_cubicBoxEdges]
  simp only [positiveInternalBoxEdges, Finset.filter_map, Finset.card_map]
  rfl

theorem positiveInfiniteClusterInteriorEdgeAverage_eq_count_div
    (d n : ℕ) (omega : EdgeConfiguration d) :
    positiveInfiniteClusterInteriorEdgeAverage d
        (cubicMetricBox d cubicOrigin n) omega =
      (positiveBoxInteriorEdgeCount d n omega : ℝ) /
        (cubicMetricBox d cubicOrigin n).card := by
  classical
  unfold positiveInfiniteClusterInteriorEdgeAverage
  simp_rw [translatedInfiniteClusterInteriorPositiveEdgeAverage_eq]
  rw [← Finset.sum_div]
  congr 1
  rw [positiveBoxInteriorEdgeCount,
    cast_card_filter_eq_sum_eventIndicator, positiveBoxEdgePairs]
  exact (Finset.sum_product_right
    (cubicMetricBox d cubicOrigin n) Finset.univ
    (fun xi ↦ eventIndicator
      (infiniteClusterInteriorEdgeEvent (cubicStepEdge xi.1 (xi.2, true))) omega)).symm

theorem positiveInfiniteClusterBoundaryEdgeAverage_eq_count_div
    (d n : ℕ) (omega : EdgeConfiguration d) :
    positiveInfiniteClusterBoundaryEdgeAverage d
        (cubicMetricBox d cubicOrigin n) omega =
      (positiveBoxBoundaryEdgeCount d n omega : ℝ) /
        (cubicMetricBox d cubicOrigin n).card := by
  classical
  unfold positiveInfiniteClusterBoundaryEdgeAverage
  simp_rw [translatedInfiniteClusterBoundaryPositiveEdgeAverage_eq]
  rw [← Finset.sum_div]
  congr 1
  rw [positiveBoxBoundaryEdgeCount,
    cast_card_filter_eq_sum_eventIndicator, positiveBoxEdgePairs]
  exact (Finset.sum_product_right
    (cubicMetricBox d cubicOrigin n) Finset.univ
    (fun xi ↦ eventIndicator
      (infiniteClusterBoundaryEdgeEvent (cubicStepEdge xi.1 (xi.2, true))) omega)).symm

private theorem card_filter_internal_le_total
    {d n : ℕ} (P : Cubic d × Fin d → Prop) [DecidablePred P] :
    ((positiveInternalBoxEdgePairs d n).filter P).card ≤
      ((positiveBoxEdgePairs d n).filter P).card := by
  apply Finset.card_le_card
  intro xi hxi
  rw [Finset.mem_filter] at hxi ⊢
  exact ⟨positiveInternalBoxEdgePairs_subset_positiveBoxEdgePairs d n hxi.1, hxi.2⟩

private theorem card_filter_total_le_internal_add_outer
    {d n : ℕ} (P : Cubic d × Fin d → Prop) [DecidablePred P] :
    ((positiveBoxEdgePairs d n).filter P).card ≤
      ((positiveInternalBoxEdgePairs d n).filter P).card +
        (positiveOuterBoxEdgePairs d n).card := by
  calc
    ((positiveBoxEdgePairs d n).filter P).card ≤
        (((positiveInternalBoxEdgePairs d n).filter P) ∪
          positiveOuterBoxEdgePairs d n).card := by
      apply Finset.card_le_card
      intro xi hxi
      rw [Finset.mem_filter] at hxi
      have hpair := positiveBoxEdgePairs_subset_internal_union_outer d n hxi.1
      rcases Finset.mem_union.mp hpair with hi | ho
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hxi.2⟩)
      · exact Finset.mem_union_right _ ho
    _ ≤ ((positiveInternalBoxEdgePairs d n).filter P).card +
        (positiveOuterBoxEdgePairs d n).card := Finset.card_union_le _ _

theorem positiveBoxInteriorEdgeCount_sub_internal_le_outer
    (d n : ℕ) (omega : EdgeConfiguration d) :
    (positiveBoxInteriorEdgeCount d n omega : ℝ) -
        infiniteClusterInteriorEdgeCount d n omega ≤
      (positiveOuterBoxEdgePairs d n).card := by
  classical
  rw [infiniteClusterInteriorEdgeCount_eq_positiveInternalPairs]
  have h := card_filter_total_le_internal_add_outer
    (d := d) (n := n) (fun xi ↦ omega ∈
      infiniteClusterInteriorEdgeEvent (cubicStepEdge xi.1 (xi.2, true)))
  unfold positiveBoxInteriorEdgeCount
  unfold positiveInternalBoxInteriorEdgeCount
  apply sub_le_iff_le_add.mpr
  exact_mod_cast h.trans_eq (Nat.add_comm _ _)

theorem positiveBoxBoundaryEdgeCount_sub_internal_le_outer
    (d n : ℕ) (omega : EdgeConfiguration d) :
    (positiveBoxBoundaryEdgeCount d n omega : ℝ) -
        infiniteClusterBoundaryEdgeCount d n omega ≤
      (positiveOuterBoxEdgePairs d n).card := by
  classical
  rw [infiniteClusterBoundaryEdgeCount_eq_positiveInternalPairs]
  have h := card_filter_total_le_internal_add_outer
    (d := d) (n := n) (fun xi ↦ omega ∈
      infiniteClusterBoundaryEdgeEvent (cubicStepEdge xi.1 (xi.2, true)))
  unfold positiveBoxBoundaryEdgeCount
  unfold positiveInternalBoxBoundaryEdgeCount
  apply sub_le_iff_le_add.mpr
  exact_mod_cast h.trans_eq (Nat.add_comm _ _)

theorem infiniteClusterInteriorEdgeCount_le_positiveBoxCount
    (d n : ℕ) (omega : EdgeConfiguration d) :
    infiniteClusterInteriorEdgeCount d n omega ≤
      positiveBoxInteriorEdgeCount d n omega := by
  classical
  rw [infiniteClusterInteriorEdgeCount_eq_positiveInternalPairs]
  unfold positiveInternalBoxInteriorEdgeCount positiveBoxInteriorEdgeCount
  exact card_filter_internal_le_total fun xi ↦ omega ∈
    infiniteClusterInteriorEdgeEvent (cubicStepEdge xi.1 (xi.2, true))

theorem infiniteClusterBoundaryEdgeCount_le_positiveBoxCount
    (d n : ℕ) (omega : EdgeConfiguration d) :
    infiniteClusterBoundaryEdgeCount d n omega ≤
      positiveBoxBoundaryEdgeCount d n omega := by
  classical
  rw [infiniteClusterBoundaryEdgeCount_eq_positiveInternalPairs]
  unfold positiveInternalBoxBoundaryEdgeCount positiveBoxBoundaryEdgeCount
  exact card_filter_internal_le_total fun xi ↦ omega ∈
    infiniteClusterBoundaryEdgeEvent (cubicStepEdge xi.1 (xi.2, true))

theorem abs_infiniteClusterInteriorEdgeDensity_sub_positiveAverage_le
    (d n : ℕ) (omega : EdgeConfiguration d) :
    |infiniteClusterInteriorEdgeDensity d n omega -
        positiveInfiniteClusterInteriorEdgeAverage d
          (cubicMetricBox d cubicOrigin n) omega| ≤
      (positiveOuterBoxEdgePairs d n).card /
        (cubicMetricBox d cubicOrigin n).card := by
  rw [infiniteClusterInteriorEdgeDensity,
    positiveInfiniteClusterInteriorEdgeAverage_eq_count_div, abs_sub_comm,
    ← sub_div]
  have hnonneg : (0 : ℝ) ≤
      (positiveBoxInteriorEdgeCount d n omega : ℝ) -
        infiniteClusterInteriorEdgeCount d n omega := by
    exact sub_nonneg.mpr (by
      exact_mod_cast infiniteClusterInteriorEdgeCount_le_positiveBoxCount d n omega)
  rw [abs_of_nonneg (div_nonneg hnonneg (by positivity))]
  exact div_le_div_of_nonneg_right
    (positiveBoxInteriorEdgeCount_sub_internal_le_outer d n omega)
    (by positivity)

theorem abs_infiniteClusterBoundaryEdgeDensity_sub_positiveAverage_le
    (d n : ℕ) (omega : EdgeConfiguration d) :
    |infiniteClusterBoundaryEdgeDensity d n omega -
        positiveInfiniteClusterBoundaryEdgeAverage d
          (cubicMetricBox d cubicOrigin n) omega| ≤
      (positiveOuterBoxEdgePairs d n).card /
        (cubicMetricBox d cubicOrigin n).card := by
  rw [infiniteClusterBoundaryEdgeDensity,
    positiveInfiniteClusterBoundaryEdgeAverage_eq_count_div, abs_sub_comm,
    ← sub_div]
  have hnonneg : (0 : ℝ) ≤
      (positiveBoxBoundaryEdgeCount d n omega : ℝ) -
        infiniteClusterBoundaryEdgeCount d n omega := by
    exact sub_nonneg.mpr (by
      exact_mod_cast infiniteClusterBoundaryEdgeCount_le_positiveBoxCount d n omega)
  rw [abs_of_nonneg (div_nonneg hnonneg (by positivity))]
  exact div_le_div_of_nonneg_right
    (positiveBoxBoundaryEdgeCount_sub_internal_le_outer d n omega)
    (by positivity)

/-- The deterministic discrepancy between all positive edges based in a box and the internal
box-edge set is a vanishing surface-to-volume term. -/
theorem positiveOuterBoxEdgePairs_card_div_boxCard_tendsto_zero
    {d : ℕ} (hd : 1 ≤ d) :
    Tendsto
      (fun n : ℕ ↦ ((positiveOuterBoxEdgePairs d n).card : ℝ) /
        (cubicMetricBox d cubicOrigin n).card)
      atTop (nhds 0) := by
  let C : ℝ := 2 * d * d
  have hden : Tendsto (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_atTop_mono'
      atTop (Eventually.of_forall fun n ↦ by
        show (n : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ)
        exact_mod_cast (show n ≤ 2 * n + 1 by omega))
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ ↦ C / ((2 * n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := hden.const_div_atTop C
  have hle : ∀ᶠ n : ℕ in atTop,
      ((positiveOuterBoxEdgePairs d n).card : ℝ) /
          (cubicMetricBox d cubicOrigin n).card ≤
        C / ((2 * n + 1 : ℕ) : ℝ) :=
    Eventually.of_forall fun n ↦ by
      rw [cubicMetricBox_card]
      have houter := positiveOuterBoxEdgePairs_card_le d n
      have hsurface := cubicBoxSurface_card_le (n := n)
        (Nat.zero_lt_of_lt hd) cubicOrigin
      have hcardNat : (positiveOuterBoxEdgePairs d n).card ≤
          (2 * d * (2 * n + 1) ^ (d - 1)) * d :=
        houter.trans (Nat.mul_le_mul_right d hsurface)
      have hcard : ((positiveOuterBoxEdgePairs d n).card : ℝ) ≤
          ((2 * d * (2 * n + 1) ^ (d - 1)) * d : ℕ) := by
        exact_mod_cast hcardNat
      apply (div_le_div_of_nonneg_right hcard (by positivity)).trans_eq
      dsimp only [C]
      push_cast
      have hpow : (2 * (n : ℝ) + 1) ^ (d - 1) *
          (2 * (n : ℝ) + 1) = (2 * (n : ℝ) + 1) ^ d := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      field_simp
      nlinarith
  exact squeeze_zero'
    (Eventually.of_forall fun n ↦ div_nonneg (by positivity) (by positivity))
    hle hupper

/-- One of the endpoints of the reference edge reaches its radius-`r` coordinate-box surface. -/
def positiveEdgeRadiusContinuationEvent (d : ℕ) (i : Fin d) (r : ℕ) :
    Set (EdgeConfiguration d) :=
  ⋃ x ∈ (positiveCoordinateEdge d i).1.toFinset,
    boxRadiusConnectionEvent d x r

/-- Finite support for the reference-edge radius event and the state of the edge itself. -/
noncomputable def positiveEdgeRadiusSupport (d : ℕ) (i : Fin d) (r : ℕ) :
    Finset (CubicEdge d) := by
  classical
  exact {positiveCoordinateEdge d i} ∪
    (positiveCoordinateEdge d i).1.toFinset.biUnion fun x ↦ cubicBoxEdges d x r

/-- Open-edge cylinder approximation to the infinite-cluster interior-edge event. -/
def infiniteClusterInteriorEdgeRadiusApproxEvent (d : ℕ) (i : Fin d) (r : ℕ) :
    Set (EdgeConfiguration d) :=
  positiveEdgeRadiusContinuationEvent d i r ∩
    finiteCylinder {positiveCoordinateEdge d i} {positiveCoordinateEdge d i}

/-- Closed-edge cylinder approximation to the infinite-cluster boundary-edge event. -/
def infiniteClusterBoundaryEdgeRadiusApproxEvent (d : ℕ) (i : Fin d) (r : ℕ) :
    Set (EdgeConfiguration d) :=
  positiveEdgeRadiusContinuationEvent d i r ∩
    finiteCylinder {positiveCoordinateEdge d i} ∅

theorem dependsOn_positiveEdgeRadiusContinuationEvent
    (d : ℕ) (i : Fin d) (r : ℕ) :
    DependsOn (positiveEdgeRadiusSupport d i r)
      (positiveEdgeRadiusContinuationEvent d i r) := by
  classical
  intro omega eta hagree
  simp only [positiveEdgeRadiusContinuationEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hxe, hx⟩
    refine ⟨x, hxe, ?_⟩
    apply ((dependsOn_boxRadiusConnectionEvent d x r) (fun f hf ↦ hagree f (by
      simp only [positiveEdgeRadiusSupport, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion]
      exact Or.inr ⟨x, hxe, hf⟩))).mp hx
  · rintro ⟨x, hxe, hx⟩
    refine ⟨x, hxe, ?_⟩
    apply ((dependsOn_boxRadiusConnectionEvent d x r) (fun f hf ↦ hagree f (by
      simp only [positiveEdgeRadiusSupport, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion]
      exact Or.inr ⟨x, hxe, hf⟩))).mpr hx

theorem dependsOn_infiniteClusterInteriorEdgeRadiusApproxEvent
    (d : ℕ) (i : Fin d) (r : ℕ) :
    DependsOn (positiveEdgeRadiusSupport d i r)
      (infiniteClusterInteriorEdgeRadiusApproxEvent d i r) := by
  apply (dependsOn_positiveEdgeRadiusContinuationEvent d i r).inter
  intro omega eta hagree
  simp only [mem_finiteCylinder]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  exact iff_congr (hagree e (by
    simp only [Finset.mem_singleton] at he
    subst e
    simp [positiveEdgeRadiusSupport])) Iff.rfl

theorem dependsOn_infiniteClusterBoundaryEdgeRadiusApproxEvent
    (d : ℕ) (i : Fin d) (r : ℕ) :
    DependsOn (positiveEdgeRadiusSupport d i r)
      (infiniteClusterBoundaryEdgeRadiusApproxEvent d i r) := by
  apply (dependsOn_positiveEdgeRadiusContinuationEvent d i r).inter
  intro omega eta hagree
  simp only [mem_finiteCylinder]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  exact iff_congr (hagree e (by
    simp only [Finset.mem_singleton] at he
    subst e
    simp [positiveEdgeRadiusSupport])) Iff.rfl

theorem endpoint_positiveCoordinateEdge_lInfDist_le_one
    {d : ℕ} (i : Fin d) {x : Cubic d}
    (hx : x ∈ (positiveCoordinateEdge d i).1.toFinset) :
    cubicLInfDist cubicOrigin x ≤ 1 := by
  have hx' : x ∈ (positiveCoordinateEdge d i : Sym2 (Cubic d)) := by
    simpa only [Sym2.mem_toFinset] using hx
  rw [positiveCoordinateEdge, cubicStepEdge, Sym2.mem_iff] at hx'
  rcases hx' with rfl | rfl
  · simp
  · exact cubicLInfDist_stepFrom_le_one cubicOrigin (i, true)

theorem endpoint_mem_positiveEdgeRadiusSupport_lInfDist_le
    {d r : ℕ} (i : Fin d) {e : CubicEdge d}
    (he : e ∈ positiveEdgeRadiusSupport d i r)
    {z : Cubic d} (hz : z ∈ (e : Sym2 (Cubic d))) :
    cubicLInfDist cubicOrigin z ≤ r + 1 := by
  classical
  simp only [positiveEdgeRadiusSupport, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion] at he
  rcases he with rfl | ⟨x, hxe, heBox⟩
  · exact (endpoint_positiveCoordinateEdge_lInfDist_le_one i
      (by simpa only [Sym2.mem_toFinset] using hz)).trans (by omega)
  · have hzBox := endpoint_mem_cubicMetricBox_of_edge_mem_cubicBoxEdges heBox hz
    have hxz : cubicLInfDist x z ≤ r :=
      mem_cubicMetricBox_iff_lInfDist_le.mp hzBox
    exact (cubicLInfDist_triangle cubicOrigin x z).trans
      (by
        have hx0 := endpoint_positiveCoordinateEdge_lInfDist_le_one i hxe
        omega)

theorem cubicEdgeSetRadius_positiveEdgeRadiusSupport_le
    (d : ℕ) (i : Fin d) (r : ℕ) :
    cubicEdgeSetRadius (positiveEdgeRadiusSupport d i r) ≤ r + 1 := by
  classical
  unfold cubicEdgeSetRadius
  apply Finset.sup_le
  intro e he
  apply max_le
  · exact endpoint_mem_positiveEdgeRadiusSupport_lInfDist_le i he (by
      exact Sym2.out_fst_mem e.1)
  · exact endpoint_mem_positiveEdgeRadiusSupport_lInfDist_le i he (by
      exact Sym2.out_snd_mem e.1)

/-- Centered finite-radius event at an arbitrary vertex. -/
def finiteBoxRadiusEventAt (d : ℕ) (x : Cubic d) (r : ℕ) :
    Set (EdgeConfiguration d) :=
  boxRadiusConnectionEvent d x r ∩
    {omega | ¬hasInfiniteOpenClusterFrom d omega x}

theorem measurableSet_finiteBoxRadiusEventAt
    (d : ℕ) (x : Cubic d) (r : ℕ) :
    MeasurableSet (finiteBoxRadiusEventAt d x r) :=
  (measurableSet_boxRadiusConnectionEvent d x r).inter
    (measurableSet_hasInfiniteOpenClusterFrom d x).compl

theorem translatedCylinderEvent_finiteBoxRadiusEvent
    (d r : ℕ) (x : Cubic d) :
    translatedCylinderEvent x (finiteBoxRadiusEvent d r) =
      finiteBoxRadiusEventAt d x r := by
  ext omega
  change cubicTranslationConfigurationPullback cubicOrigin x omega ∈
      finiteBoxRadiusEvent d r ↔ omega ∈ finiteBoxRadiusEventAt d x r
  rw [finiteBoxRadiusEvent, finiteBoxRadiusEventAt,
    connectionToBoxSurfaceEvent_origin_eq_boxRadiusConnectionEvent,
    Set.mem_inter_iff, Set.mem_inter_iff,
    cubicTranslationConfigurationPullback_mem_boxRadiusConnectionEvent_iff]
  change _ ∧ (cubicOpenCluster d
    (cubicTranslationConfigurationPullback cubicOrigin x omega)).Finite ↔ _
  rw [show (cubicOpenCluster d
      (cubicTranslationConfigurationPullback cubicOrigin x omega)).Finite ↔
        ¬hasInfiniteOpenClusterFrom d
          (cubicTranslationConfigurationPullback cubicOrigin x omega) cubicOrigin by
    rw [hasInfiniteOpenClusterFrom_origin]
    exact Set.not_infinite.symm]
  rw [cubicTranslationConfigurationPullback_hasInfiniteOpenClusterFrom_iff]
  simp

theorem finiteBoxRadiusEventAt_probability
    (d r : ℕ) (p : I) (x : Cubic d) :
    (bernoulliBondMeasure d p).real (finiteBoxRadiusEventAt d x r) =
      finiteBoxRadiusProbability d p r := by
  rw [← translatedCylinderEvent_finiteBoxRadiusEvent]
  exact bernoulliBondMeasure_real_translatedEvent
    (measurableSet_finiteBoxRadiusEvent d r) p x

/-- An infinite cluster reaches every finite coordinate-box surface around its root. -/
theorem hasInfiniteOpenClusterFrom_mem_boxRadiusConnectionEvent
    {d r : ℕ} {omega : EdgeConfiguration d} {x : Cubic d}
    (hx : hasInfiniteOpenClusterFrom d omega x) :
    omega ∈ boxRadiusConnectionEvent d x r := by
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection]
  have houtside : ∃ y ∈ cubicOpenClusterFrom d omega x,
      y ∉ cubicMetricBox d x r := by
    by_contra hnot
    push Not at hnot
    apply hx
    exact (cubicMetricBox d x r).finite_toSet.subset fun y hy ↦ hnot y hy
  obtain ⟨y, ⟨w, hwOpen⟩, hyBox⟩ := houtside
  have hry : r ≤ cubicLInfDist x y := by
    exact le_of_not_ge fun hle ↦
      hyBox (mem_cubicMetricBox_iff_lInfDist_le.mpr hle)
  obtain ⟨z, hzSurface, hzConnection⟩ :=
    exists_open_walk_to_cubicBoxSurface_in_box w hwOpen hry
  exact ⟨z, hzSurface, connectionEventIn_subset d _ x z hzConnection⟩

theorem infiniteClusterInteriorEdgeEvent_subset_radiusApprox
    (d : ℕ) (i : Fin d) (r : ℕ) :
    infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i) ⊆
      infiniteClusterInteriorEdgeRadiusApproxEvent d i r := by
  intro omega homega
  rw [mem_infiniteClusterInteriorEdgeEvent_iff] at homega
  rcases homega with ⟨heOpen, x, hxe, hxInf⟩
  constructor
  · simp only [positiveEdgeRadiusContinuationEvent, Set.mem_iUnion]
    exact ⟨x, hxe, hasInfiniteOpenClusterFrom_mem_boxRadiusConnectionEvent hxInf⟩
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    simp [heOpen]

theorem infiniteClusterBoundaryEdgeEvent_subset_radiusApprox
    (d : ℕ) (i : Fin d) (r : ℕ) :
    infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i) ⊆
      infiniteClusterBoundaryEdgeRadiusApproxEvent d i r := by
  intro omega homega
  rw [mem_infiniteClusterBoundaryEdgeEvent_iff] at homega
  rcases homega with ⟨heClosed, x, hxe, hxInf⟩
  constructor
  · simp only [positiveEdgeRadiusContinuationEvent, Set.mem_iUnion]
    exact ⟨x, hxe, hasInfiniteOpenClusterFrom_mem_boxRadiusConnectionEvent hxInf⟩
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    simp [heClosed]

theorem interiorEdgeRadiusApprox_symmDiff_subset_finiteRadius
    (d : ℕ) (i : Fin d) (r : ℕ) :
    infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i) ∆
        infiniteClusterInteriorEdgeRadiusApproxEvent d i r ⊆
      ⋃ x ∈ (positiveCoordinateEdge d i).1.toFinset,
        finiteBoxRadiusEventAt d x r := by
  intro omega homega
  rw [Set.mem_symmDiff] at homega
  rcases homega with homega | homega
  · exact (homega.2
      (infiniteClusterInteriorEdgeEvent_subset_radiusApprox d i r homega.1)).elim
  · rcases homega with ⟨⟨hradius, hcylinder⟩, hnotInfiniteEdge⟩
    simp only [positiveEdgeRadiusContinuationEvent, Set.mem_iUnion] at hradius ⊢
    rcases hradius with ⟨x, hxe, hxRadius⟩
    refine ⟨x, hxe, hxRadius, ?_⟩
    intro hxInf
    apply hnotInfiniteEdge
    rw [mem_infiniteClusterInteriorEdgeEvent_iff]
    refine ⟨?_, x, hxe, hxInf⟩
    exact (mem_finiteCylinder.mp hcylinder
      (positiveCoordinateEdge d i) (by simp)).mpr (by simp)

theorem boundaryEdgeRadiusApprox_symmDiff_subset_finiteRadius
    (d : ℕ) (i : Fin d) (r : ℕ) :
    infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i) ∆
        infiniteClusterBoundaryEdgeRadiusApproxEvent d i r ⊆
      ⋃ x ∈ (positiveCoordinateEdge d i).1.toFinset,
        finiteBoxRadiusEventAt d x r := by
  intro omega homega
  rw [Set.mem_symmDiff] at homega
  rcases homega with homega | homega
  · exact (homega.2
      (infiniteClusterBoundaryEdgeEvent_subset_radiusApprox d i r homega.1)).elim
  · rcases homega with ⟨⟨hradius, hcylinder⟩, hnotInfiniteEdge⟩
    simp only [positiveEdgeRadiusContinuationEvent, Set.mem_iUnion] at hradius ⊢
    rcases hradius with ⟨x, hxe, hxRadius⟩
    refine ⟨x, hxe, hxRadius, ?_⟩
    intro hxInf
    apply hnotInfiniteEdge
    rw [mem_infiniteClusterBoundaryEdgeEvent_iff]
    refine ⟨?_, x, hxe, hxInf⟩
    intro heOpen
    have := (mem_finiteCylinder.mp hcylinder
      (positiveCoordinateEdge d i) (by simp)).mp heOpen
    simp at this

theorem interiorEdgeRadiusApprox_symmDiff_probability_le
    (d : ℕ) (i : Fin d) (r : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real
        (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i) ∆
          infiniteClusterInteriorEdgeRadiusApproxEvent d i r) ≤
      2 * finiteBoxRadiusProbability d p r := by
  calc
    _ ≤ (bernoulliBondMeasure d p).real
        (⋃ x ∈ (positiveCoordinateEdge d i).1.toFinset,
          finiteBoxRadiusEventAt d x r) :=
      measureReal_mono (h₂ := measure_ne_top _ _)
        (interiorEdgeRadiusApprox_symmDiff_subset_finiteRadius d i r)
    _ ≤ ∑ x ∈ (positiveCoordinateEdge d i).1.toFinset,
        (bernoulliBondMeasure d p).real (finiteBoxRadiusEventAt d x r) :=
      measureReal_biUnion_finset_le _ _
    _ = 2 * finiteBoxRadiusProbability d p r := by
      simp_rw [finiteBoxRadiusEventAt_probability]
      rw [Finset.sum_const, nsmul_eq_mul,
        Sym2.card_toFinset_of_not_isDiag _
          ((cubicGraph d).not_isDiag_of_mem_edgeSet
            (positiveCoordinateEdge d i).2)]
      ring

theorem boundaryEdgeRadiusApprox_symmDiff_probability_le
    (d : ℕ) (i : Fin d) (r : ℕ) (p : I) :
    (bernoulliBondMeasure d p).real
        (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i) ∆
          infiniteClusterBoundaryEdgeRadiusApproxEvent d i r) ≤
      2 * finiteBoxRadiusProbability d p r := by
  calc
    _ ≤ (bernoulliBondMeasure d p).real
        (⋃ x ∈ (positiveCoordinateEdge d i).1.toFinset,
          finiteBoxRadiusEventAt d x r) :=
      measureReal_mono (h₂ := measure_ne_top _ _)
        (boundaryEdgeRadiusApprox_symmDiff_subset_finiteRadius d i r)
    _ ≤ ∑ x ∈ (positiveCoordinateEdge d i).1.toFinset,
        (bernoulliBondMeasure d p).real (finiteBoxRadiusEventAt d x r) :=
      measureReal_biUnion_finset_le _ _
    _ = 2 * finiteBoxRadiusProbability d p r := by
      simp_rw [finiteBoxRadiusEventAt_probability]
      rw [Finset.sum_const, nsmul_eq_mul,
        Sym2.card_toFinset_of_not_isDiag _
          ((cubicGraph d).not_isDiag_of_mem_edgeSet
            (positiveCoordinateEdge d i).2)]
      ring

theorem summable_succ_pow_mul_exp_neg
    {d : ℕ} {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ d *
      Real.exp (-(n : ℝ) * a) := by
  let q := Real.exp (-a)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0, Real.exp_lt_one_iff]
    linarith
  have hpow : Summable fun n : ℕ ↦ (n : ℝ) ^ d * q ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one d hq1
  have hgeom : Summable fun n : ℕ ↦ q ^ n :=
    summable_geometric_of_norm_lt_one hq1
  have hmajor : Summable fun n : ℕ ↦
      q ^ n + (2 : ℝ) ^ d * ((n : ℝ) ^ d * q ^ n) :=
    hgeom.add (hpow.mul_left ((2 : ℝ) ^ d))
  apply hmajor.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have hexp : Real.exp (-(n : ℝ) * a) = q ^ n := by
      dsimp only [q]
      rw [show -(n : ℝ) * a = (n : ℝ) * (-a) by ring,
        Real.exp_nat_mul]
    rw [hexp]
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hbase : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        push_cast
        linarith
      have hpowLe := pow_le_pow_left₀ (by positivity) hbase d
      rw [mul_pow] at hpowLe
      have hqnonneg : 0 ≤ q ^ n := pow_nonneg hq0.le n
      calc
        ((n + 1 : ℕ) : ℝ) ^ d * q ^ n ≤
            ((2 : ℝ) ^ d * (n : ℝ) ^ d) * q ^ n :=
          mul_le_mul_of_nonneg_right hpowLe hqnonneg
        _ ≤ q ^ n + (2 : ℝ) ^ d * ((n : ℝ) ^ d * q ^ n) := by
          nlinarith [pow_nonneg hq0.le n]

theorem summable_finiteBoxRadiusProbability_of_rate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    Summable (finiteBoxRadiusProbability d p) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_finiteBoxRadiusProbability_le_succ_pow_mul_exp_neg_rate hd p hp0 hp1
  have hmajor := (summable_succ_pow_mul_exp_neg (d := d) hrate).mul_left A
  apply hmajor.of_nonneg_of_le
  · exact finiteBoxRadiusProbability_nonneg d p
  · intro n
    simpa only [mul_assoc] using hbound n

theorem summable_interiorEdgeRadiusApprox_error_of_rate_pos
    {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    Summable fun r : ℕ ↦
      (bernoulliBondMeasure d p).real
        (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i) ∆
          infiniteClusterInteriorEdgeRadiusApproxEvent d i r) := by
  apply ((summable_finiteBoxRadiusProbability_of_rate_pos hd p hp0 hp1 hrate).mul_left 2).of_nonneg_of_le
  · intro r
    exact measureReal_nonneg
  · intro r
    exact interiorEdgeRadiusApprox_symmDiff_probability_le d i r p

theorem summable_boundaryEdgeRadiusApprox_error_of_rate_pos
    {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    Summable fun r : ℕ ↦
      (bernoulliBondMeasure d p).real
        (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i) ∆
          infiniteClusterBoundaryEdgeRadiusApproxEvent d i r) := by
  apply ((summable_finiteBoxRadiusProbability_of_rate_pos hd p hp0 hp1 hrate).mul_left 2).of_nonneg_of_le
  · intro r
    exact measureReal_nonneg
  · intro r
    exact boundaryEdgeRadiusApprox_symmDiff_probability_le d i r p

/-- Square radii are the deterministic averaging subsequence used by the strong-law proof. -/
def squareRadius (n : ℕ) : ℕ := n ^ 2

theorem summable_positiveEdgeRadiusSupport_varianceCost
    {d : ℕ} (hd : 2 ≤ d) (i : Fin d) :
    Summable fun n : ℕ ↦
      ((((2 * (2 * cubicEdgeSetRadius (positiveEdgeRadiusSupport d i n)) + 1) ^ d : ℕ) : ℝ) /
        (cubicMetricBox d cubicOrigin (squareRadius n)).card) := by
  have hpseries : Summable fun n : ℕ ↦
      (5 : ℝ) ^ d * (1 / |(n : ℝ) + 1| ^ (d : ℝ)) := by
    apply Summable.mul_left
    exact (Real.summable_one_div_nat_add_rpow 1 d).2 (by exact_mod_cast hd)
  apply hpseries.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hradius := cubicEdgeSetRadius_positiveEdgeRadiusSupport_le d i n
  have hnumNat : 2 * (2 * cubicEdgeSetRadius (positiveEdgeRadiusSupport d i n)) + 1 ≤
      5 * (n + 1) := by omega
  have hdenNat : (n + 1) ^ 2 ≤ 2 * n ^ 2 + 1 := by nlinarith
  rw [cubicMetricBox_card, squareRadius]
  have hnum :
      (((2 * (2 * cubicEdgeSetRadius (positiveEdgeRadiusSupport d i n)) + 1) ^ d : ℕ) : ℝ) ≤
        ((((5 * (n + 1)) ^ d : ℕ)) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_left hnumNat d
  have hden : (((((n + 1) ^ 2) ^ d : ℕ)) : ℝ) ≤
      ((((2 * n ^ 2 + 1) ^ d : ℕ)) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_left hdenNat d
  have hdenPos : (0 : ℝ) < (((((n + 1) ^ 2) ^ d : ℕ)) : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  have hratio :
      (((2 * (2 * cubicEdgeSetRadius (positiveEdgeRadiusSupport d i n)) + 1) ^ d : ℕ) : ℝ) /
          ((((2 * n ^ 2 + 1) ^ d : ℕ)) : ℝ) ≤
          ((((5 * (n + 1)) ^ d : ℕ)) : ℝ) /
          (((((n + 1) ^ 2) ^ d : ℕ)) : ℝ) := by
    calc
      _ ≤ ((((5 * (n + 1)) ^ d : ℕ)) : ℝ) /
          ((((2 * n ^ 2 + 1) ^ d : ℕ)) : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ ((((5 * (n + 1)) ^ d : ℕ)) : ℝ) /
          (((((n + 1) ^ 2) ^ d : ℕ)) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hdenPos hden
  calc
    _ ≤ ((((5 * (n + 1)) ^ d : ℕ)) : ℝ) /
          (((((n + 1) ^ 2) ^ d : ℕ)) : ℝ) := hratio
    _ = (5 : ℝ) ^ d * (1 / |(n : ℝ) + 1| ^ (d : ℝ)) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
      push_cast
      rw [Real.rpow_natCast]
      field_simp
      rw [← mul_pow, ← mul_pow]
      congr 1
      ring

/-- Almost-sure square-box law for the positively oriented infinite-cluster interior edge in
direction `i`.  The finite-radius decay exponent is the only percolation input: it makes the
cylinder-approximation errors summable. -/
theorem translatedInfiniteClusterInteriorEdgeAverage_square_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ translatedEventAverage
          (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i))
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop
        (nhds ((bernoulliBondMeasure d p).real
          (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i)))) := by
  apply translatedEventAverage_tendsto_ae_of_summable_cylinderApprox
    p (measurable_infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i))
    (positiveEdgeRadiusSupport d i)
    (infiniteClusterInteriorEdgeRadiusApproxEvent d i)
    (dependsOn_infiniteClusterInteriorEdgeRadiusApproxEvent d i)
    (fun n ↦ cubicMetricBox d cubicOrigin (squareRadius n))
  · intro n
    exact ⟨cubicOrigin, mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)⟩
  · exact summable_interiorEdgeRadiusApprox_error_of_rate_pos
      hd i p hp0 hp1 hrate
  · exact summable_positiveEdgeRadiusSupport_varianceCost hd i

/-- Almost-sure square-box law for the positively oriented boundary edge touching an infinite
cluster. -/
theorem translatedInfiniteClusterBoundaryEdgeAverage_square_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ translatedEventAverage
          (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i))
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop
        (nhds ((bernoulliBondMeasure d p).real
          (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i)))) := by
  apply translatedEventAverage_tendsto_ae_of_summable_cylinderApprox
    p (measurable_infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i))
    (positiveEdgeRadiusSupport d i)
    (infiniteClusterBoundaryEdgeRadiusApproxEvent d i)
    (dependsOn_infiniteClusterBoundaryEdgeRadiusApproxEvent d i)
    (fun n ↦ cubicMetricBox d cubicOrigin (squareRadius n))
  · intro n
    exact ⟨cubicOrigin, mem_cubicMetricBox_iff_lInfDist_le.mpr (by simp)⟩
  · exact summable_boundaryEdgeRadiusApprox_error_of_rate_pos
      hd i p hp0 hp1 hrate
  · exact summable_positiveEdgeRadiusSupport_varianceCost hd i

private theorem tendsto_finset_sum_real
    {α : Type*} {l : Filter ℕ} (s : Finset α)
    (f : α → ℕ → ℝ) (a : α → ℝ)
    (h : ∀ x ∈ s, Tendsto (f x) l (nhds (a x))) :
    Tendsto (fun n ↦ ∑ x ∈ s, f x n) l (nhds (∑ x ∈ s, a x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact tendsto_const_nhds
  | @insert x s hxs ih =>
      simp only [Finset.sum_insert hxs]
      exact (h x (by simp)).add
        (ih fun y hy ↦ h y (by simp [hy]))

/-- Almost-sure square-box law for the total positively oriented interior-edge field. -/
theorem positiveInfiniteClusterInteriorEdgeAverage_square_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ positiveInfiniteClusterInteriorEdgeAverage d
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop (nhds (infiniteClusterInteriorEdgeIntensity d p)) := by
  have hEach : ∀ i : Fin d, ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ translatedEventAverage
          (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i))
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop
        (nhds ((bernoulliBondMeasure d p).real
          (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i)))) :=
    fun i ↦
      translatedInfiniteClusterInteriorEdgeAverage_square_tendsto_ae_of_radiusRate_pos
        hd i p hp0 hp1 hrate
  have hAll : ∀ᵐ omega ∂bernoulliBondMeasure d p, ∀ i : Fin d,
      Tendsto
        (fun n ↦ translatedEventAverage
          (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i))
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop
        (nhds ((bernoulliBondMeasure d p).real
          (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i)))) :=
    ae_all_iff.mpr hEach
  filter_upwards [hAll] with omega homega
  simpa only [positiveInfiniteClusterInteriorEdgeAverage,
    infiniteClusterInteriorEdgeIntensity, positiveCoordinateEdge] using
    tendsto_finset_sum_real Finset.univ
      (fun i n ↦ translatedEventAverage
        (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i))
        (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
      (fun i ↦ (bernoulliBondMeasure d p).real
        (infiniteClusterInteriorEdgeEvent (positiveCoordinateEdge d i)))
      (fun i _hi ↦ homega i)

/-- Almost-sure square-box law for the total positively oriented boundary-edge field. -/
theorem positiveInfiniteClusterBoundaryEdgeAverage_square_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ positiveInfiniteClusterBoundaryEdgeAverage d
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop (nhds (infiniteClusterBoundaryEdgeIntensity d p)) := by
  have hEach : ∀ i : Fin d, ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ translatedEventAverage
          (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i))
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop
        (nhds ((bernoulliBondMeasure d p).real
          (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i)))) :=
    fun i ↦
      translatedInfiniteClusterBoundaryEdgeAverage_square_tendsto_ae_of_radiusRate_pos
        hd i p hp0 hp1 hrate
  have hAll : ∀ᵐ omega ∂bernoulliBondMeasure d p, ∀ i : Fin d,
      Tendsto
        (fun n ↦ translatedEventAverage
          (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i))
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
        atTop
        (nhds ((bernoulliBondMeasure d p).real
          (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i)))) :=
    ae_all_iff.mpr hEach
  filter_upwards [hAll] with omega homega
  simpa only [positiveInfiniteClusterBoundaryEdgeAverage,
    infiniteClusterBoundaryEdgeIntensity, positiveCoordinateEdge] using
    tendsto_finset_sum_real Finset.univ
      (fun i n ↦ translatedEventAverage
        (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i))
        (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
      (fun i ↦ (bernoulliBondMeasure d p).real
        (infiniteClusterBoundaryEdgeEvent (positiveCoordinateEdge d i)))
      (fun i _hi ↦ homega i)

private theorem squareRadius_tendsto_atTop : Tendsto squareRadius atTop atTop := by
  exact tendsto_atTop_mono'
    atTop
    (by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      change n ≤ n ^ 2
      nlinarith)
    tendsto_id

private theorem natSqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  exact ⟨N ^ 2, fun n hn ↦ Nat.le_sqrt'.mpr hn⟩

/-- Consecutive square-radius box volumes are asymptotically equal. -/
private theorem squareBoxVolume_ratio_tendsto_one (d : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin (squareRadius n)).card : ℝ) /
          (cubicMetricBox d cubicOrigin (squareRadius (n + 1))).card)
      atTop (nhds 1) := by
  let b : ℕ → ℝ := fun n ↦
    ((2 * n ^ 2 + 1 : ℕ) : ℝ) / ((2 * (n + 1) ^ 2 + 1 : ℕ) : ℝ)
  have hupper : Tendsto (fun n : ℕ ↦ (2 : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 - b n :=
    Eventually.of_forall fun n ↦ by
        dsimp only [b]
        apply sub_nonneg.mpr
        apply (div_le_one (by positivity)).2
        have hsquare : n ^ 2 ≤ (n + 1) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        exact_mod_cast (by omega : 2 * n ^ 2 + 1 ≤ 2 * (n + 1) ^ 2 + 1)
  have hle : ∀ᶠ n : ℕ in atTop,
      1 - b n ≤ (2 : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    Eventually.of_forall fun n ↦ by
        dsimp only [b]
        have hden : (0 : ℝ) < ((2 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) := by positivity
        rw [show (1 : ℝ) =
            ((2 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) /
              ((2 * (n + 1) ^ 2 + 1 : ℕ) : ℝ) by
          exact (div_self hden.ne').symm,
          ← sub_div, div_le_div_iff₀ hden (by positivity)]
        push_cast
        ring_nf
        nlinarith
  have hdiff : Tendsto (fun n ↦ 1 - b n) atTop (nhds 0) :=
    squeeze_zero' hnonneg hle hupper
  have hb : Tendsto b atTop (nhds 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub hdiff using 1 <;>
      simp [sub_sub_cancel, b]
  convert hb.pow d using 1
  · funext n
    rw [cubicMetricBox_card, cubicMetricBox_card]
    dsimp only [b]
    simp only [squareRadius, div_pow, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  · norm_num

private theorem squareBoxVolume_reverseRatio_tendsto_one (d : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        ((cubicMetricBox d cubicOrigin (squareRadius (n + 1))).card : ℝ) /
          (cubicMetricBox d cubicOrigin (squareRadius n)).card)
      atTop (nhds 1) := by
  have h := (squareBoxVolume_ratio_tendsto_one d).inv₀ (by norm_num)
  convert h using 1
  · funext n
    rw [inv_div]
  · norm_num

/-- Monotone raw counts whose volume-normalized values converge along square radii converge
along all radii.  This deterministic interpolation is the Følner-sequence step used below. -/
private theorem tendsto_boxDensity_of_square_tendsto
    {d : ℕ} (C : ℕ → ℕ) (hC : Monotone C) {L : ℝ}
    (hsquare : Tendsto
      (fun n ↦ (C (squareRadius n) : ℝ) /
        (cubicMetricBox d cubicOrigin (squareRadius n)).card)
      atTop (nhds L)) :
    Tendsto
      (fun n ↦ (C n : ℝ) / (cubicMetricBox d cubicOrigin n).card)
      atTop (nhds L) := by
  let k : ℕ → ℕ := Nat.sqrt
  let V : ℕ → ℝ := fun n ↦ (cubicMetricBox d cubicOrigin n).card
  have hk : Tendsto k atTop atTop := natSqrt_tendsto_atTop
  have hkSucc : Tendsto (fun n ↦ k n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hk
  have hlowerT : Tendsto
      (fun n ↦ ((C (squareRadius (k n)) : ℝ) / V (squareRadius (k n))) *
        (V (squareRadius (k n)) / V (squareRadius (k n + 1))))
      atTop (nhds L) := by
    simpa using (hsquare.comp hk).mul
      ((squareBoxVolume_ratio_tendsto_one d).comp hk)
  have hupperT : Tendsto
      (fun n ↦ ((C (squareRadius (k n + 1)) : ℝ) /
          V (squareRadius (k n + 1))) *
        (V (squareRadius (k n + 1)) / V (squareRadius (k n))))
      atTop (nhds L) := by
    simpa using (hsquare.comp hkSucc).mul
      ((squareBoxVolume_reverseRatio_tendsto_one d).comp hk)
  have hlower : ∀ n : ℕ,
      ((C (squareRadius (k n)) : ℝ) / V (squareRadius (k n))) *
          (V (squareRadius (k n)) / V (squareRadius (k n + 1))) ≤
        (C n : ℝ) / V n := by
    intro n
    have hkn : squareRadius (k n) ≤ n := Nat.sqrt_le' n
    have hnk : n ≤ squareRadius (k n + 1) := by
      exact Nat.le_of_lt (Nat.sqrt_lt'.mp (Nat.lt_succ_self (k n)))
    have hCkn : C (squareRadius (k n)) ≤ C n := hC hkn
    have hVn : V n ≤ V (squareRadius (k n + 1)) := by
      dsimp only [V]
      rw [cubicMetricBox_card, cubicMetricBox_card]
      exact_mod_cast Nat.pow_le_pow_left (by omega : 2 * n + 1 ≤
        2 * squareRadius (k n + 1) + 1) d
    have hVpos (m : ℕ) : 0 < V m := by
      dsimp only [V]
      rw [cubicMetricBox_card]
      positivity
    rw [show ((C (squareRadius (k n)) : ℝ) / V (squareRadius (k n))) *
        (V (squareRadius (k n)) / V (squareRadius (k n + 1))) =
      (C (squareRadius (k n)) : ℝ) / V (squareRadius (k n + 1)) by
        field_simp [ne_of_gt (hVpos (squareRadius (k n)))] ]
    calc
      (C (squareRadius (k n)) : ℝ) / V (squareRadius (k n + 1)) ≤
          (C (squareRadius (k n)) : ℝ) / V n :=
        div_le_div_of_nonneg_left (by positivity) (hVpos n) hVn
      _ ≤ (C n : ℝ) / V n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hCkn) (hVpos n).le
  have hupper : ∀ n : ℕ,
      (C n : ℝ) / V n ≤
        ((C (squareRadius (k n + 1)) : ℝ) / V (squareRadius (k n + 1))) *
          (V (squareRadius (k n + 1)) / V (squareRadius (k n))) := by
    intro n
    have hkn : squareRadius (k n) ≤ n := Nat.sqrt_le' n
    have hnk : n ≤ squareRadius (k n + 1) := by
      exact Nat.le_of_lt (Nat.sqrt_lt'.mp (Nat.lt_succ_self (k n)))
    have hCnk : C n ≤ C (squareRadius (k n + 1)) := hC hnk
    have hVk : V (squareRadius (k n)) ≤ V n := by
      dsimp only [V]
      rw [cubicMetricBox_card, cubicMetricBox_card]
      exact_mod_cast Nat.pow_le_pow_left (by omega :
        2 * squareRadius (k n) + 1 ≤ 2 * n + 1) d
    have hVpos (m : ℕ) : 0 < V m := by
      dsimp only [V]
      rw [cubicMetricBox_card]
      positivity
    rw [show ((C (squareRadius (k n + 1)) : ℝ) /
        V (squareRadius (k n + 1))) *
          (V (squareRadius (k n + 1)) / V (squareRadius (k n))) =
        (C (squareRadius (k n + 1)) : ℝ) / V (squareRadius (k n)) by
      field_simp [ne_of_gt (hVpos (squareRadius (k n + 1)))] ]
    calc
      (C n : ℝ) / V n ≤ (C n : ℝ) / V (squareRadius (k n)) :=
        div_le_div_of_nonneg_left (by positivity)
          (hVpos (squareRadius (k n))) hVk
      _ ≤ (C (squareRadius (k n + 1)) : ℝ) / V (squareRadius (k n)) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hCnk)
          (hVpos (squareRadius (k n))).le
  exact hlowerT.squeeze' hupperT
    (Eventually.of_forall hlower) (Eventually.of_forall hupper)

/-- The actual internal-edge density has the same square-box limit as the positive oriented
stationary field; their deterministic discrepancy is supported on the box surface. -/
theorem infiniteClusterInteriorEdgeDensity_square_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ infiniteClusterInteriorEdgeDensity d (squareRadius n) omega)
        atTop (nhds (infiniteClusterInteriorEdgeIntensity d p)) := by
  have haverage :=
    positiveInfiniteClusterInteriorEdgeAverage_square_tendsto_ae_of_radiusRate_pos
      hd p hp0 hp1 hrate
  have hsurface :=
    (positiveOuterBoxEdgePairs_card_div_boxCard_tendsto_zero
      (show 1 ≤ d by omega)).comp squareRadius_tendsto_atTop
  filter_upwards [haverage] with omega homega
  have hnorm : Tendsto
      (fun n ↦ |infiniteClusterInteriorEdgeDensity d (squareRadius n) omega -
        positiveInfiniteClusterInteriorEdgeAverage d
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall fun n ↦
        abs_infiniteClusterInteriorEdgeDensity_sub_positiveAverage_le
          d (squareRadius n) omega
    · exact hsurface
  have hdiff : Tendsto
      (fun n ↦ infiniteClusterInteriorEdgeDensity d (squareRadius n) omega -
        positiveInfiniteClusterInteriorEdgeAverage d
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using hnorm
  convert hdiff.add homega using 1 <;> simp

/-- Square-box boundary-edge density law. -/
theorem infiniteClusterBoundaryEdgeDensity_square_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto
        (fun n ↦ infiniteClusterBoundaryEdgeDensity d (squareRadius n) omega)
        atTop (nhds (infiniteClusterBoundaryEdgeIntensity d p)) := by
  have haverage :=
    positiveInfiniteClusterBoundaryEdgeAverage_square_tendsto_ae_of_radiusRate_pos
      hd p hp0 hp1 hrate
  have hsurface :=
    (positiveOuterBoxEdgePairs_card_div_boxCard_tendsto_zero
      (show 1 ≤ d by omega)).comp squareRadius_tendsto_atTop
  filter_upwards [haverage] with omega homega
  have hnorm : Tendsto
      (fun n ↦ |infiniteClusterBoundaryEdgeDensity d (squareRadius n) omega -
        positiveInfiniteClusterBoundaryEdgeAverage d
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall fun n ↦
        abs_infiniteClusterBoundaryEdgeDensity_sub_positiveAverage_le
          d (squareRadius n) omega
    · exact hsurface
  have hdiff : Tendsto
      (fun n ↦ infiniteClusterBoundaryEdgeDensity d (squareRadius n) omega -
        positiveInfiniteClusterBoundaryEdgeAverage d
          (cubicMetricBox d cubicOrigin (squareRadius n)) omega)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using hnorm
  convert hdiff.add homega using 1 <;> simp

theorem infiniteClusterInteriorEdgeCount_monotone
    (d : ℕ) (omega : EdgeConfiguration d) :
    Monotone (fun n ↦ infiniteClusterInteriorEdgeCount d n omega) := by
  classical
  intro n m hnm
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨cubicBoxEdges_mono_radius hnm he.1, he.2⟩

theorem infiniteClusterBoundaryEdgeCount_monotone
    (d : ℕ) (omega : EdgeConfiguration d) :
    Monotone (fun n ↦ infiniteClusterBoundaryEdgeCount d n omega) := by
  classical
  intro n m hnm
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨cubicBoxEdges_mono_radius hnm he.1, he.2⟩

/-- Almost-sure internal-edge density law along every coordinate-box radius. -/
theorem infiniteClusterInteriorEdgeDensity_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ infiniteClusterInteriorEdgeDensity d n omega)
        atTop (nhds (infiniteClusterInteriorEdgeIntensity d p)) := by
  filter_upwards [
    infiniteClusterInteriorEdgeDensity_square_tendsto_ae_of_radiusRate_pos
      hd p hp0 hp1 hrate] with omega homega
  apply tendsto_boxDensity_of_square_tendsto
    (fun n ↦ infiniteClusterInteriorEdgeCount d n omega)
    (infiniteClusterInteriorEdgeCount_monotone d omega)
  simpa only [infiniteClusterInteriorEdgeDensity] using homega

/-- Almost-sure boundary-edge density law along every coordinate-box radius. -/
theorem infiniteClusterBoundaryEdgeDensity_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ infiniteClusterBoundaryEdgeDensity d n omega)
        atTop (nhds (infiniteClusterBoundaryEdgeIntensity d p)) := by
  filter_upwards [
    infiniteClusterBoundaryEdgeDensity_square_tendsto_ae_of_radiusRate_pos
      hd p hp0 hp1 hrate] with omega homega
  apply tendsto_boxDensity_of_square_tendsto
    (fun n ↦ infiniteClusterBoundaryEdgeCount d n omega)
    (infiniteClusterBoundaryEdgeCount_monotone d omega)
  simpa only [infiniteClusterBoundaryEdgeDensity] using homega

/-- Discharge the specialized pointwise density hypothesis in Theorem 8.99 from the positive
finite-cluster radius exponent.  This replaces the unavailable multiparameter pointwise
ergodic theorem by finite-cylinder approximation, Borel--Cantelli, and square interpolation. -/
theorem infiniteClusterEdgeDensityLimits_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    InfiniteClusterEdgeDensityLimits d p := by
  filter_upwards [
    infiniteClusterInteriorEdgeDensity_tendsto_ae_of_radiusRate_pos
      hd p hp0 hp1 hrate,
    infiniteClusterBoundaryEdgeDensity_tendsto_ae_of_radiusRate_pos
      hd p hp0 hp1 hrate] with omega hinterior hboundary
  exact ⟨hinterior, hboundary⟩

/-- **Grimmett, Theorem 8.99**, conditional only on the positive finite-cluster radius exponent
which is the conclusion of Theorem 8.21. -/
theorem infiniteClusterBoundaryInteriorEdgeRatio_tendsto_ae_of_radiusRate_pos
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (htheta : 0 < theta d p)
    (hrate : 0 < finiteClusterRadiusDecayRate d p) :
    ∀ᵐ omega ∂bernoulliBondMeasure d p,
      Tendsto (fun n ↦ infiniteClusterBoundaryInteriorEdgeRatio d n omega)
        atTop (nhds ((1 - (p : ℝ)) / (p : ℝ))) :=
  infiniteClusterBoundaryInteriorEdgeRatio_tendsto_ae_of_densityLimits
    (show 1 ≤ d by omega) p hp0 htheta
    (infiniteClusterEdgeDensityLimits_of_radiusRate_pos hd p hp0 hp1 hrate)

end Percolation
