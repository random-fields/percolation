import Percolation.Bernoulli.FiniteEventContinuity
import Percolation.Critical.DynamicRenormalization

/-!
# Half-space bricks

Dimension-uniform brick and facet geometry for Grimmett's half-space block construction.  The
facet indexing specializes in dimension three to four top orthants and eight side subfacets.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The horizontal coordinate associated with `i : Fin (d-1)`. -/
def brickHorizontalIndex {d : ℕ} (hd : 1 ≤ d) (i : Fin (d - 1)) : Fin d :=
  ⟨i.val, by omega⟩

/-- The vertical (last) coordinate. -/
def brickVerticalIndex {d : ℕ} (hd : 1 ≤ d) : Fin d :=
  ⟨d - 1, by omega⟩

/-- The half-space brick `[-L,L]^(d-1) × [0,H]`. -/
noncomputable def halfSpaceBrick (d L H : ℕ) : Finset (Cubic d) :=
  Fintype.piFinset fun i : Fin d ↦
    if i.val + 1 = d then Finset.Icc 0 (H : ℤ)
    else Finset.Icc (-(L : ℤ)) (L : ℤ)

@[simp]
theorem mem_halfSpaceBrick_iff {d L H : ℕ} {x : Cubic d} :
    x ∈ halfSpaceBrick d L H ↔
      ∀ i : Fin d,
        if i.val + 1 = d then 0 ≤ x i ∧ x i ≤ (H : ℤ)
        else -(L : ℤ) ≤ x i ∧ x i ≤ (L : ℤ) := by
  classical
  simp only [halfSpaceBrick, Fintype.mem_piFinset]
  constructor <;> intro h i
  · specialize h i
    split_ifs at h ⊢ <;> simpa using h
  · specialize h i
    split_ifs at h ⊢ <;> simpa using h

/-- Subfacets used by the brick exploration.  A top facet is split into horizontal orthants.
Each signed side face is split into a lower and upper half. -/
inductive BrickFacetKind (d : ℕ)
  | top (orthant : Fin (d - 1) → Bool)
  | side (normal : Fin (d - 1)) (positive upper : Bool)
  deriving DecidableEq, Fintype

/-- Explicit finite encoding used to count brick subfacets. -/
def brickFacetKindEquiv (d : ℕ) :
    BrickFacetKind d ≃ (Fin (d - 1) → Bool) ⊕ (Fin (d - 1) × (Bool × Bool)) where
  toFun
    | .top orthant => Sum.inl orthant
    | .side normal positive upper => Sum.inr (normal, (positive, upper))
  invFun
    | Sum.inl orthant => .top orthant
    | Sum.inr (normal, (positive, upper)) => .side normal positive upper
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with x | ⟨normal, positive, upper⟩ <;> rfl

theorem brickFacetKind_card (d : ℕ) :
    Fintype.card (BrickFacetKind d) = 2 ^ (d - 1) + 4 * (d - 1) := by
  rw [Fintype.card_congr (brickFacetKindEquiv d)]
  simp
  ring

example : Fintype.card (BrickFacetKind 3) = 12 := by native_decide

/-- Placement of a brick by a cubic-lattice graph automorphism.  Concrete explorations use the
translation and signed-coordinate-permutation isomorphisms from `CubicSymmetry`. -/
structure RotatedBrickPlacement (d : ℕ) where
  iso : cubicGraph d ≃g cubicGraph d

/-- Vertex set of a placed brick. -/
noncomputable def RotatedBrickPlacement.vertices {d : ℕ}
    (P : RotatedBrickPlacement d) (L H : ℕ) : Finset (Cubic d) := by
  classical
  exact (halfSpaceBrick d L H).image P.iso

/-- Vertices in one selected brick subfacet. -/
noncomputable def brickFacet {d : ℕ} (hd : 1 ≤ d) (L H : ℕ)
    (kind : BrickFacetKind d) : Finset (Cubic d) := by
  classical
  exact (halfSpaceBrick d L H).filter fun x ↦
    match kind with
    | .top orthant =>
        x (brickVerticalIndex hd) = (H : ℤ) ∧
          ∀ i : Fin (d - 1),
            if orthant i then 0 ≤ x (brickHorizontalIndex hd i)
            else x (brickHorizontalIndex hd i) ≤ 0
    | .side normal positive upper =>
        x (brickHorizontalIndex hd normal) =
            (if positive then (L : ℤ) else -(L : ℤ)) ∧
          (if upper then (H : ℤ) ≤ 2 * x (brickVerticalIndex hd)
           else 2 * x (brickVerticalIndex hd) ≤ (H : ℤ))

@[simp]
theorem mem_brickFacet_iff {d : ℕ} (hd : 1 ≤ d) {L H : ℕ}
    {kind : BrickFacetKind d} {x : Cubic d} :
    x ∈ brickFacet hd L H kind ↔ x ∈ halfSpaceBrick d L H ∧
      match kind with
      | .top orthant =>
          x (brickVerticalIndex hd) = (H : ℤ) ∧
            ∀ i : Fin (d - 1),
              if orthant i then 0 ≤ x (brickHorizontalIndex hd i)
              else x (brickHorizontalIndex hd i) ≤ 0
      | .side normal positive upper =>
          x (brickHorizontalIndex hd normal) =
              (if positive then (L : ℤ) else -(L : ℤ)) ∧
            (if upper then (H : ℤ) ≤ 2 * x (brickVerticalIndex hd)
             else 2 * x (brickVerticalIndex hd) ≤ (H : ℤ)) := by
  classical
  simp [brickFacet]

/-- Vertex set of a placed brick subfacet. -/
noncomputable def RotatedBrickPlacement.facet {d : ℕ}
    (P : RotatedBrickPlacement d) (hd : 1 ≤ d) (L H : ℕ)
    (kind : BrickFacetKind d) : Finset (Cubic d) := by
  classical
  exact (brickFacet hd L H kind).image P.iso

/-- A codimension-one seed plane centered at `c`, orthogonal to coordinate `normal`. -/
noncomputable def brickSeedPlane {d : ℕ} (c : Cubic d) (normal : Fin d) (m : ℕ) :
    Finset (Cubic d) :=
  (cubicMetricBox d c m).filter fun x ↦ x normal = c normal

/-- Edges internal to a finite seed plane. -/
noncomputable def brickSeedPlaneEdges {d : ℕ} (c : Cubic d) (normal : Fin d) (m : ℕ) :
    Finset (CubicEdge d) :=
  (cubicBoxEdges d c m).filter fun e ↦
    e.1.out.1 ∈ brickSeedPlane c normal m ∧ e.1.out.2 ∈ brickSeedPlane c normal m

/-- Every bond of a finite seed plane is open. -/
def brickSeedPlaneEvent {d : ℕ} (c : Cubic d) (normal : Fin d) (m : ℕ) :
    Set (EdgeConfiguration d) :=
  openEdgeSetEvent d (brickSeedPlaneEdges c normal m)

theorem measurableSet_brickSeedPlaneEvent {d : ℕ}
    (c : Cubic d) (normal : Fin d) (m : ℕ) :
    MeasurableSet (brickSeedPlaneEvent c normal m) :=
  measurableSet_openEdgeSetEvent d _

theorem isIncreasingEvent_brickSeedPlaneEvent {d : ℕ}
    (c : Cubic d) (normal : Fin d) (m : ℕ) :
    IsIncreasingEvent (brickSeedPlaneEvent c normal m) := by
  intro ω η hωη hω e he
  exact hωη (hω he)

/-- Edges with both endpoints in a half-space brick. -/
noncomputable def halfSpaceBrickEdges (d L H : ℕ) : Finset (CubicEdge d) := by
  classical
  exact (cubicBoxEdges d cubicOrigin (max L H)).filter fun e ↦
    e.1.out.1 ∈ halfSpaceBrick d L H ∧ e.1.out.2 ∈ halfSpaceBrick d L H

/-- Edges usable by the brick exploration.  Bonds lying wholly in the underside are excluded;
the initial seed is represented by its vertex set, rather than by revealing those underside
bonds. -/
noncomputable def halfSpaceBrickUsableEdges {d : ℕ} (hd : 1 ≤ d) (L H : ℕ) :
    Finset (CubicEdge d) := by
  classical
  exact (halfSpaceBrickEdges d L H).filter fun e ↦
    ¬(e.1.out.1 (brickVerticalIndex hd) = 0 ∧
      e.1.out.2 (brickVerticalIndex hd) = 0)

theorem not_both_vertical_zero_of_mem_halfSpaceBrickUsableEdges {d : ℕ}
    (hd : 1 ≤ d) {L H : ℕ} {e : CubicEdge d}
    (he : e ∈ halfSpaceBrickUsableEdges hd L H) :
    ¬(e.1.out.1 (brickVerticalIndex hd) = 0 ∧
      e.1.out.2 (brickVerticalIndex hd) = 0) := by
  classical
  simpa [halfSpaceBrickUsableEdges] using (Finset.mem_filter.mp he).2

/-- The normal to a seed parallel to the selected brick facet. -/
def brickFacetSeedNormal {d : ℕ} (hd : 1 ≤ d) : BrickFacetKind d → Fin d
  | .top _ => brickVerticalIndex hd
  | .side normal _ _ => brickHorizontalIndex hd normal

/-- Centers whose entire seed plane lies in the selected subfacet.  This explicit filter is
important when the seed radius is comparable with the facet dimensions. -/
noncomputable def brickFacetSeedCenters {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ)
    (kind : BrickFacetKind d) : Finset (Cubic d) := by
  classical
  exact (brickFacet hd L H kind).filter fun y ↦
    brickSeedPlane y (brickFacetSeedNormal hd kind) m ⊆ brickFacet hd L H kind

theorem brickSeedPlane_subset_facet_of_mem_seedCenters {d : ℕ} (hd : 1 ≤ d)
    {m L H : ℕ} {kind : BrickFacetKind d} {y : Cubic d}
    (hy : y ∈ brickFacetSeedCenters hd m L H kind) :
    brickSeedPlane y (brickFacetSeedNormal hd kind) m ⊆ brickFacet hd L H kind := by
  classical
  exact (Finset.mem_filter.mp hy).2

/-- The initial seed square `b(0)` on the underside of the brick. -/
noncomputable def brickCentralSeedPlane {d : ℕ} (hd : 1 ≤ d) (m : ℕ) :
    Finset (Cubic d) :=
  brickSeedPlane cubicOrigin (brickVerticalIndex hd) m

/-- A connection from the initial seed square to a target seed square, using no underside
edge.  Endpoints range over the two seed vertex sets; fixing their centers as endpoints would
make the event artificially require bonds adjacent to those distinguished vertices. -/
def brickSeedConnectionEvent {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ)
    (kind : BrickFacetKind d) (y : Cubic d) : Set (EdgeConfiguration d) :=
  ⋃ z ∈ brickCentralSeedPlane hd m,
    ⋃ t ∈ brickSeedPlane y (brickFacetSeedNormal hd kind) m,
      connectionEventIn d (halfSpaceBrickUsableEdges hd L H) z t

/-- Finite-volume goodness event: the initial seed square connects, without underside bonds,
to a fully open seed square contained in every required subfacet. -/
def halfSpaceBrickGoodEvent {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ) :
    Set (EdgeConfiguration d) :=
  ⋂ kind : BrickFacetKind d,
    ⋃ y ∈ brickFacetSeedCenters hd m L H kind,
      brickSeedPlaneEvent y (brickFacetSeedNormal hd kind) m ∩
        brickSeedConnectionEvent hd m L H kind y

/-- A finite edge support deciding the good-brick event. -/
noncomputable def halfSpaceBrickGoodSupport {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ) :
    Finset (CubicEdge d) := by
  classical
  exact halfSpaceBrickUsableEdges hd L H ∪
    (Finset.univ : Finset (BrickFacetKind d)).biUnion fun kind ↦
      (brickFacetSeedCenters hd m L H kind).biUnion fun y ↦
        brickSeedPlaneEdges y (brickFacetSeedNormal hd kind) m

theorem dependsOn_brickSeedConnectionEvent {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ)
    (kind : BrickFacetKind d) (y : Cubic d) :
    DependsOn (halfSpaceBrickUsableEdges hd L H)
      (brickSeedConnectionEvent hd m L H kind y) := by
  classical
  intro ω η hagree
  simp only [brickSeedConnectionEvent, Set.mem_iUnion]
  constructor <;> intro h
  · obtain ⟨z, hz, t, ht, hconn⟩ := h
    exact ⟨z, hz, t, ht,
      (dependsOn_connectionEventIn d (halfSpaceBrickUsableEdges hd L H) z t hagree).mp hconn⟩
  · obtain ⟨z, hz, t, ht, hconn⟩ := h
    exact ⟨z, hz, t, ht,
      (dependsOn_connectionEventIn d (halfSpaceBrickUsableEdges hd L H) z t hagree).mpr hconn⟩

theorem dependsOn_halfSpaceBrickGoodEvent {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ) :
    DependsOn (halfSpaceBrickGoodSupport hd m L H)
      (halfSpaceBrickGoodEvent hd m L H) := by
  classical
  intro ω η hagree
  have hagreeBrick : ∀ e ∈ halfSpaceBrickUsableEdges hd L H, (e ∈ ω ↔ e ∈ η) := by
    intro e he
    exact hagree e (Finset.mem_union_left _ he)
  have hagreeSeed : ∀ (kind : BrickFacetKind d) (y : Cubic d),
      y ∈ brickFacetSeedCenters hd m L H kind →
      ∀ e ∈ brickSeedPlaneEdges y (brickFacetSeedNormal hd kind) m,
        (e ∈ ω ↔ e ∈ η) := by
    intro kind y hy e he
    apply hagree e
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨kind, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨y, hy, he⟩
  simp only [halfSpaceBrickGoodEvent, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hω kind
    obtain ⟨y, hy, hyseed, hyconn⟩ := hω kind
    refine ⟨y, hy, ?_, ?_⟩
    · intro e he
      exact (hagreeSeed kind y hy e he).mp (hyseed he)
    · exact (dependsOn_brickSeedConnectionEvent hd m L H kind y hagreeBrick).mp hyconn
  · intro hη kind
    obtain ⟨y, hy, hyseed, hyconn⟩ := hη kind
    refine ⟨y, hy, ?_, ?_⟩
    · intro e he
      exact (hagreeSeed kind y hy e he).mpr (hyseed he)
    · exact (dependsOn_brickSeedConnectionEvent hd m L H kind y hagreeBrick).mpr hyconn

theorem measurableSet_halfSpaceBrickGoodEvent {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ) :
    MeasurableSet (halfSpaceBrickGoodEvent hd m L H) := by
  apply MeasurableSet.iInter
  intro kind
  apply (brickFacetSeedCenters hd m L H kind).measurableSet_biUnion
  intro y _hy
  exact (measurableSet_brickSeedPlaneEvent y (brickFacetSeedNormal hd kind) m).inter
    (dependsOn_brickSeedConnectionEvent hd m L H kind y).measurableSet

theorem continuous_halfSpaceBrickGoodProbability {d : ℕ}
    (hd : 1 ≤ d) (m L H : ℕ) :
    Continuous fun x : ℝ ↦
      (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one x)).real
        (halfSpaceBrickGoodEvent hd m L H) :=
  (dependsOn_halfSpaceBrickGoodEvent hd m L H).continuous_bernoulliBondMeasure_real

theorem exists_lower_density_halfSpaceBrickGoodProbability_gt {d : ℕ}
    (hd : 1 ≤ d) (m L H : ℕ) {p : I} (hp0 : 0 < (p : ℝ)) {a : ℝ}
    (ha : a < (bernoulliBondMeasure d p).real (halfSpaceBrickGoodEvent hd m L H)) :
    ∃ q : I, (q : ℝ) < (p : ℝ) ∧
      a < (bernoulliBondMeasure d q).real (halfSpaceBrickGoodEvent hd m L H) := by
  let f : ℝ → ℝ := fun x ↦
    (bernoulliBondMeasure d (Set.projIcc 0 1 zero_le_one x)).real
      (halfSpaceBrickGoodEvent hd m L H)
  have hf : Continuous f := continuous_halfSpaceBrickGoodProbability hd m L H
  have hfp : a < f (p : ℝ) := by
    simpa [f, Set.projIcc_of_mem zero_le_one p.2] using ha
  obtain ⟨q, hqp, hq⟩ := exists_unitInterval_lt_of_continuous_gt hf hp0 hfp
  refine ⟨q, hqp, ?_⟩
  simpa [f, Set.projIcc_of_mem zero_le_one q.2] using hq

theorem isIncreasingEvent_halfSpaceBrickGoodEvent {d : ℕ}
    (hd : 1 ≤ d) (m L H : ℕ) :
    IsIncreasingEvent (halfSpaceBrickGoodEvent hd m L H) := by
  intro ω η hωη hω
  simp only [halfSpaceBrickGoodEvent, brickSeedConnectionEvent, Set.mem_iInter,
    Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
  intro kind
  obtain ⟨y, hyfacet, hyseed, hyconn⟩ := hω kind
  exact ⟨y, hyfacet,
    isIncreasingEvent_brickSeedPlaneEvent y (brickFacetSeedNormal hd kind) m hωη hyseed,
    by
      obtain ⟨z, hz, t, ht, hzt⟩ := hyconn
      exact ⟨z, hz, t, ht,
        isIncreasingEvent_connectionEventIn d (halfSpaceBrickUsableEdges hd L H) z t
          hωη hzt⟩⟩

end Percolation
