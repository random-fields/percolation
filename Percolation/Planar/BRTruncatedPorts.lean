import Percolation.Planar.BRFiberGeometry
import Percolation.Planar.BRTruncatedBoundary

/-!
# Ports of the truncated BR boundary

This module identifies the four geometric sides on which a retained stopped-boundary bond can
meet the boundary of the finite dual frame.  It also describes the bottom and top ports as
adjacent changes of the reached-face predicate.  For an admissible exploration fiber, these
descriptions show that both horizontal port sets have odd cardinality.
-/

namespace Percolation

noncomputable section

/-! ### The four raw port finsets -/

/-- Retained horizontal dual bonds on the bottom row of the exploration frame. -/
def brTruncatedBottomBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (0 : Fin 2) ∧ d.base 1 = -(n : ℤ)

/-- Retained horizontal dual bonds on the top row of the exploration frame. -/
def brTruncatedTopBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (0 : Fin 2) ∧ d.base 1 = (n : ℤ) - 1

/-- Retained vertical dual bonds on the left column of the exploration frame. -/
def brTruncatedLeftBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (1 : Fin 2) ∧ d.base 0 = -1

/-- Retained vertical dual bonds on the right column of the exploration frame. -/
def brTruncatedRightBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge :=
  (brTruncatedDualBoundaryPositiveEdges n R).filter fun d ↦
    d.axis = (1 : Fin 2) ∧ d.base 0 = 2 * (n : ℤ)

@[simp]
theorem mem_brTruncatedBottomBoundaryEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge} :
    d ∈ brTruncatedBottomBoundaryEdges n R ↔
      d ∈ brTruncatedDualBoundaryPositiveEdges n R ∧
        d.axis = (0 : Fin 2) ∧ d.base 1 = -(n : ℤ) := by
  simp [brTruncatedBottomBoundaryEdges]

@[simp]
theorem mem_brTruncatedTopBoundaryEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge} :
    d ∈ brTruncatedTopBoundaryEdges n R ↔
      d ∈ brTruncatedDualBoundaryPositiveEdges n R ∧
        d.axis = (0 : Fin 2) ∧ d.base 1 = (n : ℤ) - 1 := by
  simp [brTruncatedTopBoundaryEdges]

@[simp]
theorem mem_brTruncatedLeftBoundaryEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge} :
    d ∈ brTruncatedLeftBoundaryEdges n R ↔
      d ∈ brTruncatedDualBoundaryPositiveEdges n R ∧
        d.axis = (1 : Fin 2) ∧ d.base 0 = -1 := by
  simp [brTruncatedLeftBoundaryEdges]

@[simp]
theorem mem_brTruncatedRightBoundaryEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge} :
    d ∈ brTruncatedRightBoundaryEdges n R ↔
      d ∈ brTruncatedDualBoundaryPositiveEdges n R ∧
        d.axis = (1 : Fin 2) ∧ d.base 0 = 2 * (n : ℤ) := by
  simp [brTruncatedRightBoundaryEdges]

/-! ### Coordinate bounds and disjointness -/

theorem brTruncatedBottomBoundaryEdges_base_bounds
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge}
    (hd : d ∈ brTruncatedBottomBoundaryEdges n R) :
    -1 ≤ d.base 0 ∧ d.base 0 < 2 * (n : ℤ) := by
  have hport := mem_brTruncatedBottomBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbase := mem_brLeftmostDualFaces_iff.mp htrunc.2.1
  have hstep := mem_brLeftmostDualFaces_iff.mp htrunc.2.2.1
  rw [hport.2.1] at hstep
  simp [cubicStepFrom, cubicDirectionIncrement] at hstep
  exact ⟨hbase.1, by omega⟩

theorem brTruncatedTopBoundaryEdges_base_bounds
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge}
    (hd : d ∈ brTruncatedTopBoundaryEdges n R) :
    -1 ≤ d.base 0 ∧ d.base 0 < 2 * (n : ℤ) := by
  have hport := mem_brTruncatedTopBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbase := mem_brLeftmostDualFaces_iff.mp htrunc.2.1
  have hstep := mem_brLeftmostDualFaces_iff.mp htrunc.2.2.1
  rw [hport.2.1] at hstep
  simp [cubicStepFrom, cubicDirectionIncrement] at hstep
  exact ⟨hbase.1, by omega⟩

theorem brTruncatedLeftBoundaryEdges_base_bounds
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge}
    (hd : d ∈ brTruncatedLeftBoundaryEdges n R) :
    -(n : ℤ) ≤ d.base 1 ∧ d.base 1 < (n : ℤ) - 1 := by
  have hport := mem_brTruncatedLeftBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbase := mem_brLeftmostDualFaces_iff.mp htrunc.2.1
  have hstep := mem_brLeftmostDualFaces_iff.mp htrunc.2.2.1
  have hstep1 := hstep.2.2
  rw [hport.2.1] at hstep1
  simp [cubicStepFrom, cubicDirectionIncrement] at hstep1
  exact ⟨hbase.2.2.1, by omega⟩

theorem brTruncatedRightBoundaryEdges_base_bounds
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge}
    (hd : d ∈ brTruncatedRightBoundaryEdges n R) :
    -(n : ℤ) ≤ d.base 1 ∧ d.base 1 < (n : ℤ) - 1 := by
  have hport := mem_brTruncatedRightBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbase := mem_brLeftmostDualFaces_iff.mp htrunc.2.1
  have hstep := mem_brLeftmostDualFaces_iff.mp htrunc.2.2.1
  have hstep1 := hstep.2.2
  rw [hport.2.1] at hstep1
  simp [cubicStepFrom, cubicDirectionIncrement] at hstep1
  exact ⟨hbase.2.2.1, by omega⟩

theorem disjoint_brTruncatedBottomBoundaryEdges_brTruncatedTopBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brTruncatedBottomBoundaryEdges n R)
      (brTruncatedTopBoundaryEdges n R) := by
  rw [Finset.disjoint_left]
  intro d hdBottom hdTop
  have hb := (mem_brTruncatedBottomBoundaryEdges_iff.mp hdBottom).2.2
  have ht := (mem_brTruncatedTopBoundaryEdges_iff.mp hdTop).2.2
  omega

theorem disjoint_brTruncatedBottomBoundaryEdges_brTruncatedLeftBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brTruncatedBottomBoundaryEdges n R)
      (brTruncatedLeftBoundaryEdges n R) := by
  rw [Finset.disjoint_left]
  intro d hdBottom hdLeft
  have hb := (mem_brTruncatedBottomBoundaryEdges_iff.mp hdBottom).2.1
  have hl := (mem_brTruncatedLeftBoundaryEdges_iff.mp hdLeft).2.1
  omega

theorem disjoint_brTruncatedBottomBoundaryEdges_brTruncatedRightBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brTruncatedBottomBoundaryEdges n R)
      (brTruncatedRightBoundaryEdges n R) := by
  rw [Finset.disjoint_left]
  intro d hdBottom hdRight
  have hb := (mem_brTruncatedBottomBoundaryEdges_iff.mp hdBottom).2.1
  have hr := (mem_brTruncatedRightBoundaryEdges_iff.mp hdRight).2.1
  omega

theorem disjoint_brTruncatedTopBoundaryEdges_brTruncatedLeftBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brTruncatedTopBoundaryEdges n R)
      (brTruncatedLeftBoundaryEdges n R) := by
  rw [Finset.disjoint_left]
  intro d hdTop hdLeft
  have ht := (mem_brTruncatedTopBoundaryEdges_iff.mp hdTop).2.1
  have hl := (mem_brTruncatedLeftBoundaryEdges_iff.mp hdLeft).2.1
  omega

theorem disjoint_brTruncatedTopBoundaryEdges_brTruncatedRightBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brTruncatedTopBoundaryEdges n R)
      (brTruncatedRightBoundaryEdges n R) := by
  rw [Finset.disjoint_left]
  intro d hdTop hdRight
  have ht := (mem_brTruncatedTopBoundaryEdges_iff.mp hdTop).2.1
  have hr := (mem_brTruncatedRightBoundaryEdges_iff.mp hdRight).2.1
  omega

theorem disjoint_brTruncatedLeftBoundaryEdges_brTruncatedRightBoundaryEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brTruncatedLeftBoundaryEdges n R)
      (brTruncatedRightBoundaryEdges n R) := by
  rw [Finset.disjoint_left]
  intro d hdLeft hdRight
  have hl := (mem_brTruncatedLeftBoundaryEdges_iff.mp hdLeft).2.2
  have hr := (mem_brTruncatedRightBoundaryEdges_iff.mp hdRight).2.2
  omega

/-! ### Separating reached sets have no vertical ports -/

/-- Inside the finite frame, ambient reached-face membership is exactly subtype membership in
the reached set. -/
theorem brReachedDualFace_iff_mem_of_mem_frame
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {z : DualSquareVertex}
    (hz : z ∈ brLeftmostDualFaces n) :
    brReachedDualFace n R z ↔ (⟨z, hz⟩ : BRLeftmostDualVertex n) ∈ R := by
  rw [brReachedDualFace, brReachedFaceCoordinates, Finset.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hw' : w = (⟨z, hz⟩ : BRLeftmostDualVertex n) := Subtype.ext hwz
    simpa [hw'] using hw
  · intro hzR
    exact ⟨⟨z, hz⟩, hzR, rfl⟩

theorem brTruncatedLeftBoundaryEdges_eq_empty_of_separating
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRSeparatingReachedSet n R) :
    brTruncatedLeftBoundaryEdges n R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hport := mem_brTruncatedLeftBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbaseFrame := htrunc.2.1
  have hstepFrame := htrunc.2.2.1
  have hbaseSource :
      (⟨d.base, hbaseFrame⟩ : BRLeftmostDualVertex n) ∈ brLeftmostDualSources n := by
    rw [mem_brLeftmostDualSources_iff]
    exact hport.2.2
  have hstep0 : cubicStepFrom d.base (d.axis, true) 0 = -1 := by
    rw [hport.2.1]
    simp [cubicStepFrom, cubicDirectionIncrement, hport.2.2]
  have hstepSource :
      (⟨cubicStepFrom d.base (d.axis, true), hstepFrame⟩ :
        BRLeftmostDualVertex n) ∈ brLeftmostDualSources n := by
    rw [mem_brLeftmostDualSources_iff]
    exact hstep0
  have hbaseReached : brReachedDualFace n R d.base :=
    (brReachedDualFace_iff_mem_of_mem_frame hbaseFrame).mpr (hR.1 hbaseSource)
  have hstepReached :
      brReachedDualFace n R (cubicStepFrom d.base (d.axis, true)) :=
    (brReachedDualFace_iff_mem_of_mem_frame hstepFrame).mpr (hR.1 hstepSource)
  exact htrunc.1 (iff_of_true hbaseReached hstepReached)

theorem brTruncatedRightBoundaryEdges_eq_empty_of_separating
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRSeparatingReachedSet n R) :
    brTruncatedRightBoundaryEdges n R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hport := mem_brTruncatedRightBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbaseFrame := htrunc.2.1
  have hstepFrame := htrunc.2.2.1
  have hbaseTarget :
      (⟨d.base, hbaseFrame⟩ : BRLeftmostDualVertex n) ∈ brRightmostDualTargets n := by
    rw [mem_brRightmostDualTargets_iff]
    exact hport.2.2
  have hstep0 : cubicStepFrom d.base (d.axis, true) 0 = 2 * (n : ℤ) := by
    rw [hport.2.1]
    simp [cubicStepFrom, cubicDirectionIncrement, hport.2.2]
  have hstepTarget :
      (⟨cubicStepFrom d.base (d.axis, true), hstepFrame⟩ :
        BRLeftmostDualVertex n) ∈ brRightmostDualTargets n := by
    rw [mem_brRightmostDualTargets_iff]
    exact hstep0
  have hdisjoint := Finset.disjoint_left.mp hR.2
  have hbaseNotR : (⟨d.base, hbaseFrame⟩ : BRLeftmostDualVertex n) ∉ R :=
    fun hzR ↦ hdisjoint hzR hbaseTarget
  have hstepNotR :
      (⟨cubicStepFrom d.base (d.axis, true), hstepFrame⟩ :
        BRLeftmostDualVertex n) ∉ R :=
    fun hzR ↦ hdisjoint hzR hstepTarget
  have hbaseUnreached : ¬brReachedDualFace n R d.base :=
    fun hz ↦ hbaseNotR ((brReachedDualFace_iff_mem_of_mem_frame hbaseFrame).mp hz)
  have hstepUnreached :
      ¬brReachedDualFace n R (cubicStepFrom d.base (d.axis, true)) :=
    fun hz ↦ hstepNotR ((brReachedDualFace_iff_mem_of_mem_frame hstepFrame).mp hz)
  exact htrunc.1 (iff_of_false hbaseUnreached hstepUnreached)

/-! ### Adjacent changes on the bottom and top rows -/

/-- Horizontal locations at which bottom-row reached status changes. -/
def brBottomBoundaryChangeIndices
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset ℕ :=
  adjacentChangeIndices
    (fun x : ℤ ↦ brReachedDualFace n R (squareVertex x (-(n : ℤ))))
    (-1) (2 * n + 1)

/-- Horizontal locations at which top-row reached status changes. -/
def brTopBoundaryChangeIndices
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset ℕ :=
  adjacentChangeIndices
    (fun x : ℤ ↦ brReachedDualFace n R (squareVertex x ((n : ℤ) - 1)))
    (-1) (2 * n + 1)

/-- Bottom-row change indices converted into their positive dual bonds. -/
def brBottomBoundaryChangeEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge :=
  (brBottomBoundaryChangeIndices n R).map
    (framedHorizontalPositiveEdgeEmbedding (-(n : ℤ)))

/-- Top-row change indices converted into their positive dual bonds. -/
def brTopBoundaryChangeEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset DualSquarePositiveEdge :=
  (brTopBoundaryChangeIndices n R).map
    (framedHorizontalPositiveEdgeEmbedding ((n : ℤ) - 1))

@[simp]
theorem mem_brBottomBoundaryChangeEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge} :
    d ∈ brBottomBoundaryChangeEdges n R ↔
      -1 ≤ d.base 0 ∧ d.base 0 < 2 * (n : ℤ) ∧
        d.axis = (0 : Fin 2) ∧ d.base 1 = -(n : ℤ) ∧
          brStoppedDualBoundaryEdge n R d := by
  classical
  rw [brBottomBoundaryChangeEdges, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [brBottomBoundaryChangeIndices, adjacentChangeIndices, Finset.mem_filter] at hj
    rcases hj with ⟨hjRange, hjChange⟩
    have hjlt := Finset.mem_range.mp hjRange
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [framedHorizontalPositiveEdgeEmbedding, squareVertex]
      omega
    · simp [framedHorizontalPositiveEdgeEmbedding, squareVertex]
      omega
    · simp [framedHorizontalPositiveEdgeEmbedding]
    · simp [framedHorizontalPositiveEdgeEmbedding, squareVertex]
    · simpa [brStoppedDualBoundaryEdge, framedHorizontalPositiveEdgeEmbedding,
        cubicStepFrom_squareVertex_horizontal_pos, squareVertex] using hjChange
  · rintro ⟨hxLower, hxUpper, haxis, hy, hchange⟩
    let j : ℕ := (d.base 0 + 1).toNat
    have hjCast : (j : ℤ) = d.base 0 + 1 := by
      have hnonneg : 0 ≤ d.base 0 + 1 := by omega
      simpa [j] using Int.toNat_of_nonneg hnonneg
    have hbase : d.base = squareVertex (d.base 0) (-(n : ℤ)) := by
      ext i
      fin_cases i <;> simp [squareVertex, hy]
    refine ⟨j, ?_, ?_⟩
    · rw [brBottomBoundaryChangeIndices, adjacentChangeIndices, Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · rw [brStoppedDualBoundaryEdge, haxis, hbase,
          cubicStepFrom_squareVertex_horizontal_pos] at hchange
        simpa [hjCast, squareVertex] using hchange
    · cases d with
      | mk base axis =>
          change axis = 0 at haxis
          subst axis
          change base = squareVertex (base 0) (-(n : ℤ)) at hbase
          change (j : ℤ) = base 0 + 1 at hjCast
          have hbase' : squareVertex ((j : ℤ) - 1) (-(n : ℤ)) = base := by
            rw [hbase]
            ext i
            fin_cases i <;> simp [squareVertex, hjCast]
          dsimp [framedHorizontalPositiveEdgeEmbedding]
          rw [hbase']

@[simp]
theorem mem_brTopBoundaryChangeEdges_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {d : DualSquarePositiveEdge} :
    d ∈ brTopBoundaryChangeEdges n R ↔
      -1 ≤ d.base 0 ∧ d.base 0 < 2 * (n : ℤ) ∧
        d.axis = (0 : Fin 2) ∧ d.base 1 = (n : ℤ) - 1 ∧
          brStoppedDualBoundaryEdge n R d := by
  classical
  rw [brTopBoundaryChangeEdges, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [brTopBoundaryChangeIndices, adjacentChangeIndices, Finset.mem_filter] at hj
    rcases hj with ⟨hjRange, hjChange⟩
    have hjlt := Finset.mem_range.mp hjRange
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [framedHorizontalPositiveEdgeEmbedding, squareVertex]
      omega
    · simp [framedHorizontalPositiveEdgeEmbedding, squareVertex]
      omega
    · simp [framedHorizontalPositiveEdgeEmbedding]
    · simp [framedHorizontalPositiveEdgeEmbedding, squareVertex]
    · simpa [brStoppedDualBoundaryEdge, framedHorizontalPositiveEdgeEmbedding,
        cubicStepFrom_squareVertex_horizontal_pos, squareVertex] using hjChange
  · rintro ⟨hxLower, hxUpper, haxis, hy, hchange⟩
    let j : ℕ := (d.base 0 + 1).toNat
    have hjCast : (j : ℤ) = d.base 0 + 1 := by
      have hnonneg : 0 ≤ d.base 0 + 1 := by omega
      simpa [j] using Int.toNat_of_nonneg hnonneg
    have hbase : d.base = squareVertex (d.base 0) ((n : ℤ) - 1) := by
      ext i
      fin_cases i <;> simp [squareVertex, hy]
    refine ⟨j, ?_, ?_⟩
    · rw [brTopBoundaryChangeIndices, adjacentChangeIndices, Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · rw [brStoppedDualBoundaryEdge, haxis, hbase,
          cubicStepFrom_squareVertex_horizontal_pos] at hchange
        simpa [hjCast, squareVertex] using hchange
    · cases d with
      | mk base axis =>
          change axis = 0 at haxis
          subst axis
          change base = squareVertex (base 0) ((n : ℤ) - 1) at hbase
          change (j : ℤ) = base 0 + 1 at hjCast
          have hbase' : squareVertex ((j : ℤ) - 1) ((n : ℤ) - 1) = base := by
            rw [hbase]
            ext i
            fin_cases i <;> simp [squareVertex, hjCast]
          dsimp [framedHorizontalPositiveEdgeEmbedding]
          rw [hbase']

/-- Every retained bottom port is one of the bottom-row reached-status changes. -/
theorem brTruncatedBottomBoundaryEdges_subset_changeEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    brTruncatedBottomBoundaryEdges n R ⊆ brBottomBoundaryChangeEdges n R := by
  intro d hd
  have hport := mem_brTruncatedBottomBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbounds := brTruncatedBottomBoundaryEdges_base_bounds hd
  exact mem_brBottomBoundaryChangeEdges_iff.mpr
    ⟨hbounds.1, hbounds.2, hport.2.1, hport.2.2, htrunc.1⟩

/-- Every retained top port is one of the top-row reached-status changes. -/
theorem brTruncatedTopBoundaryEdges_subset_changeEdges
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    brTruncatedTopBoundaryEdges n R ⊆ brTopBoundaryChangeEdges n R := by
  intro d hd
  have hport := mem_brTruncatedTopBoundaryEdges_iff.mp hd
  have htrunc := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp hport.1
  have hbounds := brTruncatedTopBoundaryEdges_base_bounds hd
  exact mem_brTopBoundaryChangeEdges_iff.mpr
    ⟨hbounds.1, hbounds.2, hport.2.1, hport.2.2, htrunc.1⟩

/-- On a realizable fiber, every bottom-row reached-status change survives the explicit
boundary-free edge filter. -/
theorem brBottomBoundaryChangeEdges_subset_truncated
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brBottomBoundaryChangeEdges n R ⊆ brTruncatedBottomBoundaryEdges n R := by
  rcases hR.1 with ⟨omega, homega⟩
  intro d hd
  have hchange := mem_brBottomBoundaryChangeEdges_iff.mp hd
  have hbaseFrame : d.base ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff]
    exact ⟨hchange.1, by omega, by omega, by omega⟩
  have hstepFrame :
      cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff, hchange.2.2.1]
    simp [cubicStepFrom, cubicDirectionIncrement]
    omega
  let e : BRStoppedInterfaceEdge n R := ⟨d, hchange.2.2.2.2⟩
  have hallowed :
      (dualToPrimalCrossingPositiveEdge d).toEdge ∈
        squareBoundaryFreeRectangleEdges (2 * n) n := by
    simpa [e] using
      dualToPrimalCrossingPositiveEdge_mem_boundaryFree_of_mem_fiber
        homega e hbaseFrame hstepFrame
  rw [mem_brTruncatedBottomBoundaryEdges_iff,
    mem_brTruncatedDualBoundaryPositiveEdges_iff]
  exact ⟨⟨hchange.2.2.2.2, hbaseFrame, hstepFrame, hallowed⟩,
    hchange.2.2.1, hchange.2.2.2.1⟩

/-- On a realizable fiber, every top-row reached-status change survives the explicit
boundary-free edge filter. -/
theorem brTopBoundaryChangeEdges_subset_truncated
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brTopBoundaryChangeEdges n R ⊆ brTruncatedTopBoundaryEdges n R := by
  rcases hR.1 with ⟨omega, homega⟩
  intro d hd
  have hchange := mem_brTopBoundaryChangeEdges_iff.mp hd
  have hbaseFrame : d.base ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff]
    exact ⟨hchange.1, by omega, by omega, by omega⟩
  have hstepFrame :
      cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff, hchange.2.2.1]
    simp [cubicStepFrom, cubicDirectionIncrement]
    omega
  let e : BRStoppedInterfaceEdge n R := ⟨d, hchange.2.2.2.2⟩
  have hallowed :
      (dualToPrimalCrossingPositiveEdge d).toEdge ∈
        squareBoundaryFreeRectangleEdges (2 * n) n := by
    simpa [e] using
      dualToPrimalCrossingPositiveEdge_mem_boundaryFree_of_mem_fiber
        homega e hbaseFrame hstepFrame
  rw [mem_brTruncatedTopBoundaryEdges_iff,
    mem_brTruncatedDualBoundaryPositiveEdges_iff]
  exact ⟨⟨hchange.2.2.2.2, hbaseFrame, hstepFrame, hallowed⟩,
    hchange.2.2.1, hchange.2.2.2.1⟩

theorem brTruncatedBottomBoundaryEdges_eq_changeEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brTruncatedBottomBoundaryEdges n R = brBottomBoundaryChangeEdges n R := by
  apply Finset.Subset.antisymm
  · exact brTruncatedBottomBoundaryEdges_subset_changeEdges n R
  · exact brBottomBoundaryChangeEdges_subset_truncated hn hR

theorem brTruncatedTopBoundaryEdges_eq_changeEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    brTruncatedTopBoundaryEdges n R = brTopBoundaryChangeEdges n R := by
  apply Finset.Subset.antisymm
  · exact brTruncatedTopBoundaryEdges_subset_changeEdges n R
  · exact brTopBoundaryChangeEdges_subset_truncated hn hR

theorem odd_card_brBottomBoundaryChangeIndices
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRSeparatingReachedSet n R) :
    Odd (brBottomBoundaryChangeIndices n R).card := by
  rw [brBottomBoundaryChangeIndices, odd_card_adjacentChangeIndices_iff]
  have hleftFrame :
      squareVertex (-1) (-(n : ℤ)) ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff]
    simp [squareVertex]
    omega
  have hrightFrame :
      squareVertex (2 * (n : ℤ)) (-(n : ℤ)) ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff]
    simp [squareVertex]
    omega
  have hleftSource :
      (⟨squareVertex (-1) (-(n : ℤ)), hleftFrame⟩ : BRLeftmostDualVertex n) ∈
        brLeftmostDualSources n := by
    rw [mem_brLeftmostDualSources_iff]
    simp [squareVertex]
  have hrightTarget :
      (⟨squareVertex (2 * (n : ℤ)) (-(n : ℤ)), hrightFrame⟩ :
        BRLeftmostDualVertex n) ∈ brRightmostDualTargets n := by
    rw [mem_brRightmostDualTargets_iff]
    simp [squareVertex]
  have hleft : brReachedDualFace n R (squareVertex (-1) (-(n : ℤ))) :=
    (brReachedDualFace_iff_mem_of_mem_frame hleftFrame).mpr (hR.1 hleftSource)
  have hright : ¬brReachedDualFace n R (squareVertex (2 * (n : ℤ)) (-(n : ℤ))) := by
    intro hz
    exact Finset.disjoint_left.mp hR.2
      ((brReachedDualFace_iff_mem_of_mem_frame hrightFrame).mp hz) hrightTarget
  have hend : (-1 : ℤ) + ((2 * n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) := by
    push_cast
    omega
  rw [hend]
  intro hiff
  exact hright (hiff.mp hleft)

theorem odd_card_brTopBoundaryChangeIndices
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRSeparatingReachedSet n R) :
    Odd (brTopBoundaryChangeIndices n R).card := by
  rw [brTopBoundaryChangeIndices, odd_card_adjacentChangeIndices_iff]
  have hleftFrame :
      squareVertex (-1) ((n : ℤ) - 1) ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff]
    simp [squareVertex]
    omega
  have hrightFrame :
      squareVertex (2 * (n : ℤ)) ((n : ℤ) - 1) ∈ brLeftmostDualFaces n := by
    rw [mem_brLeftmostDualFaces_iff]
    simp [squareVertex]
    omega
  have hleftSource :
      (⟨squareVertex (-1) ((n : ℤ) - 1), hleftFrame⟩ : BRLeftmostDualVertex n) ∈
        brLeftmostDualSources n := by
    rw [mem_brLeftmostDualSources_iff]
    simp [squareVertex]
  have hrightTarget :
      (⟨squareVertex (2 * (n : ℤ)) ((n : ℤ) - 1), hrightFrame⟩ :
        BRLeftmostDualVertex n) ∈ brRightmostDualTargets n := by
    rw [mem_brRightmostDualTargets_iff]
    simp [squareVertex]
  have hleft : brReachedDualFace n R (squareVertex (-1) ((n : ℤ) - 1)) :=
    (brReachedDualFace_iff_mem_of_mem_frame hleftFrame).mpr (hR.1 hleftSource)
  have hright :
      ¬brReachedDualFace n R (squareVertex (2 * (n : ℤ)) ((n : ℤ) - 1)) := by
    intro hz
    exact Finset.disjoint_left.mp hR.2
      ((brReachedDualFace_iff_mem_of_mem_frame hrightFrame).mp hz) hrightTarget
  have hend : (-1 : ℤ) + ((2 * n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) := by
    push_cast
    omega
  rw [hend]
  intro hiff
  exact hright (hiff.mp hleft)

theorem odd_card_brBottomBoundaryChangeEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRSeparatingReachedSet n R) :
    Odd (brBottomBoundaryChangeEdges n R).card := by
  rw [brBottomBoundaryChangeEdges, Finset.card_map]
  exact odd_card_brBottomBoundaryChangeIndices hn hR

theorem odd_card_brTopBoundaryChangeEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRSeparatingReachedSet n R) :
    Odd (brTopBoundaryChangeEdges n R).card := by
  rw [brTopBoundaryChangeEdges, Finset.card_map]
  exact odd_card_brTopBoundaryChangeIndices hn hR

/-- The retained bottom port set has odd cardinality on an admissible separating fiber. -/
theorem odd_card_brTruncatedBottomBoundaryEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Odd (brTruncatedBottomBoundaryEdges n R).card := by
  rw [brTruncatedBottomBoundaryEdges_eq_changeEdges hn hR]
  exact odd_card_brBottomBoundaryChangeEdges hn hR.separatingReachedSet

/-- The retained top port set has odd cardinality on an admissible separating fiber. -/
theorem odd_card_brTruncatedTopBoundaryEdges
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Odd (brTruncatedTopBoundaryEdges n R).card := by
  rw [brTruncatedTopBoundaryEdges_eq_changeEdges hn hR]
  exact odd_card_brTopBoundaryChangeEdges hn hR.separatingReachedSet

/-! ### Port finsets in the truncated graph's vertex type -/

/-- Include a raw bottom port in the vertex type of the truncated resolved boundary graph. -/
def brTruncatedBottomBoundaryVertexEmbedding
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    {d // d ∈ brTruncatedBottomBoundaryEdges n R} ↪
      BRTruncatedInterfaceEdge n R where
  toFun d := ⟨d.1, (mem_brTruncatedBottomBoundaryEdges_iff.mp d.2).1⟩
  inj' := by
    intro d e hde
    apply Subtype.ext
    exact congrArg (fun x : BRTruncatedInterfaceEdge n R ↦ x.1) hde

/-- Include a raw top port in the vertex type of the truncated resolved boundary graph. -/
def brTruncatedTopBoundaryVertexEmbedding
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    {d // d ∈ brTruncatedTopBoundaryEdges n R} ↪
      BRTruncatedInterfaceEdge n R where
  toFun d := ⟨d.1, (mem_brTruncatedTopBoundaryEdges_iff.mp d.2).1⟩
  inj' := by
    intro d e hde
    apply Subtype.ext
    exact congrArg (fun x : BRTruncatedInterfaceEdge n R ↦ x.1) hde

/-- Bottom ports, now regarded as vertices of `brTruncatedResolvedBoundaryGraph`. -/
def brTruncatedBottomBoundaryVertices
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset (BRTruncatedInterfaceEdge n R) :=
  (brTruncatedBottomBoundaryEdges n R).attach.map
    (brTruncatedBottomBoundaryVertexEmbedding n R)

/-- Top ports, now regarded as vertices of `brTruncatedResolvedBoundaryGraph`. -/
def brTruncatedTopBoundaryVertices
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset (BRTruncatedInterfaceEdge n R) :=
  (brTruncatedTopBoundaryEdges n R).attach.map
    (brTruncatedTopBoundaryVertexEmbedding n R)

@[simp]
theorem mem_brTruncatedBottomBoundaryVertices_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : BRTruncatedInterfaceEdge n R} :
    d ∈ brTruncatedBottomBoundaryVertices n R ↔
      d.1 ∈ brTruncatedBottomBoundaryEdges n R := by
  rw [brTruncatedBottomBoundaryVertices, Finset.mem_map]
  constructor
  · rintro ⟨e, _he, rfl⟩
    exact e.2
  · intro hd
    let e : {e // e ∈ brTruncatedBottomBoundaryEdges n R} := ⟨d.1, hd⟩
    refine ⟨e, by simp [e], ?_⟩
    apply Subtype.ext
    rfl

@[simp]
theorem mem_brTruncatedTopBoundaryVertices_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {d : BRTruncatedInterfaceEdge n R} :
    d ∈ brTruncatedTopBoundaryVertices n R ↔
      d.1 ∈ brTruncatedTopBoundaryEdges n R := by
  rw [brTruncatedTopBoundaryVertices, Finset.mem_map]
  constructor
  · rintro ⟨e, _he, rfl⟩
    exact e.2
  · intro hd
    let e : {e // e ∈ brTruncatedTopBoundaryEdges n R} := ⟨d.1, hd⟩
    refine ⟨e, by simp [e], ?_⟩
    apply Subtype.ext
    rfl

@[simp]
theorem card_brTruncatedBottomBoundaryVertices
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    (brTruncatedBottomBoundaryVertices n R).card =
      (brTruncatedBottomBoundaryEdges n R).card := by
  rw [brTruncatedBottomBoundaryVertices, Finset.card_map, Finset.card_attach]

@[simp]
theorem card_brTruncatedTopBoundaryVertices
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    (brTruncatedTopBoundaryVertices n R).card =
      (brTruncatedTopBoundaryEdges n R).card := by
  rw [brTruncatedTopBoundaryVertices, Finset.card_map, Finset.card_attach]

theorem disjoint_brTruncatedBottomBoundaryVertices_brTruncatedTopBoundaryVertices
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brTruncatedBottomBoundaryVertices n R)
      (brTruncatedTopBoundaryVertices n R) := by
  rw [Finset.disjoint_left]
  intro d hdBottom hdTop
  exact Finset.disjoint_left.mp
    (disjoint_brTruncatedBottomBoundaryEdges_brTruncatedTopBoundaryEdges n R)
    (mem_brTruncatedBottomBoundaryVertices_iff.mp hdBottom)
    (mem_brTruncatedTopBoundaryVertices_iff.mp hdTop)

theorem odd_card_brTruncatedBottomBoundaryVertices
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Odd (brTruncatedBottomBoundaryVertices n R).card := by
  rw [card_brTruncatedBottomBoundaryVertices]
  exact odd_card_brTruncatedBottomBoundaryEdges hn hR

theorem odd_card_brTruncatedTopBoundaryVertices
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R) :
    Odd (brTruncatedTopBoundaryVertices n R).card := by
  rw [card_brTruncatedTopBoundaryVertices]
  exact odd_card_brTruncatedTopBoundaryEdges hn hR

end

end Percolation
