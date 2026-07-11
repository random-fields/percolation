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

/-- Finite-volume goodness event: the central seed plane connects inside the brick to a fully
open seed centered at some vertex of every required subfacet. -/
def halfSpaceBrickGoodEvent {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ) :
    Set (EdgeConfiguration d) :=
  ⋂ kind : BrickFacetKind d,
    ⋃ y ∈ brickFacet hd L H kind,
      brickSeedPlaneEvent y (brickVerticalIndex hd) m ∩
        connectionEventIn d (halfSpaceBrickEdges d L H) cubicOrigin y

theorem measurableSet_halfSpaceBrickGoodEvent {d : ℕ} (hd : 1 ≤ d) (m L H : ℕ) :
    MeasurableSet (halfSpaceBrickGoodEvent hd m L H) := by
  apply MeasurableSet.iInter
  intro kind
  apply (brickFacet hd L H kind).measurableSet_biUnion
  intro y _hy
  exact (measurableSet_brickSeedPlaneEvent y (brickVerticalIndex hd) m).inter
    (dependsOn_connectionEventIn d (halfSpaceBrickEdges d L H) cubicOrigin y).measurableSet

theorem isIncreasingEvent_halfSpaceBrickGoodEvent {d : ℕ}
    (hd : 1 ≤ d) (m L H : ℕ) :
    IsIncreasingEvent (halfSpaceBrickGoodEvent hd m L H) := by
  intro ω η hωη hω
  simp only [halfSpaceBrickGoodEvent, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff] at hω ⊢
  intro kind
  obtain ⟨y, hyfacet, hyseed, hyconn⟩ := hω kind
  exact ⟨y, hyfacet,
    isIncreasingEvent_brickSeedPlaneEvent y (brickVerticalIndex hd) m hωη hyseed,
    isIncreasingEvent_connectionEventIn d (halfSpaceBrickEdges d L H) cubicOrigin y
      hωη hyconn⟩

end Percolation
