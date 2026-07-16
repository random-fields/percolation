import Percolation.Planar.AnnulusCrossings
import Percolation.Planar.AlternatingPaths
import Percolation.Planar.Crossings

/-!
# Rectangle crossings and annular circuits for RSW

These are the literal finite events in Grimmett, Section 11.7.  Rectangle crossings use no edge
whose two endpoints lie on the rectangle boundary.  A circuit surrounds the origin when its
discrete mod-two face index at the origin is one; this avoids an informal appeal to interiors in
the public Lean statement.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Whether a vertex lies on the geometric boundary of `[0,m] × [-n,n]`. -/
def squareRectangleBoundaryVertex (m n : ℕ) (x : SquareVertex) : Prop :=
  x 0 = 0 ∨ x 0 = (m : ℤ) ∨ x 1 = -(n : ℤ) ∨ x 1 = (n : ℤ)

instance squareRectangleBoundaryVertex_decidable (m n : ℕ) :
    DecidablePred (squareRectangleBoundaryVertex m n) := fun x ↦ by
  unfold squareRectangleBoundaryVertex
  infer_instance

/-- Internal rectangle bonds after removing bonds whose two endpoints both lie on the boundary. -/
noncomputable def squareBoundaryFreeRectangleEdges (m n : ℕ) : Finset SquareEdge :=
  (squareRectangleEdges m n).filter fun e ↦
    ¬ (squareRectangleBoundaryVertex m n e.1.out.1 ∧
      squareRectangleBoundaryVertex m n e.1.out.2)

/-- Grimmett's boundary-edge-free left-right crossing event. -/
def squareBoundaryFreeRectangleCrossingEvent (m n : ℕ) :
    Set (EdgeConfiguration 2) :=
  ⋃ x ∈ squareRectangleLeft m n, ⋃ y ∈ squareRectangleRight m n,
    connectionEventIn 2 (squareBoundaryFreeRectangleEdges m n) x y

theorem dependsOn_squareBoundaryFreeRectangleCrossingEvent (m n : ℕ) :
    DependsOn (squareBoundaryFreeRectangleEdges m n)
      (squareBoundaryFreeRectangleCrossingEvent m n) := by
  intro omega eta hagree
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (squareBoundaryFreeRectangleEdges m n) x y
        hagree).mp hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (squareBoundaryFreeRectangleEdges m n) x y
        hagree).mpr hxy⟩

theorem measurableSet_squareBoundaryFreeRectangleCrossingEvent (m n : ℕ) :
    MeasurableSet (squareBoundaryFreeRectangleCrossingEvent m n) :=
  (dependsOn_squareBoundaryFreeRectangleCrossingEvent m n).measurableSet

theorem isIncreasingEvent_squareBoundaryFreeRectangleCrossingEvent (m n : ℕ) :
    IsIncreasingEvent (squareBoundaryFreeRectangleCrossingEvent m n) := by
  intro omega eta hmono
  simp only [squareBoundaryFreeRectangleCrossingEvent, Set.mem_iUnion]
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    isIncreasingEvent_connectionEventIn 2 (squareBoundaryFreeRectangleEdges m n) x y
      hmono hxy⟩

/-- `LR(kl,l)` from Grimmett, translated horizontally by `l` to `[0,2kl] × [-l,l]`. -/
def rswRectangleCrossingEvent (k l : ℕ) : Set (EdgeConfiguration 2) :=
  squareBoundaryFreeRectangleCrossingEvent (2 * k * l) l

/-- `LR(l)` from Grimmett. -/
def rswSquareCrossingEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  rswRectangleCrossingEvent 1 l

/-- The `3l × 2l` left-right crossing event in Grimmett, Lemma 11.73. -/
def rswThreeHalvesCrossingEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  squareBoundaryFreeRectangleCrossingEvent (3 * l) l

theorem measurableSet_rswRectangleCrossingEvent (k l : ℕ) :
    MeasurableSet (rswRectangleCrossingEvent k l) :=
  measurableSet_squareBoundaryFreeRectangleCrossingEvent _ _

theorem isIncreasingEvent_rswRectangleCrossingEvent (k l : ℕ) :
    IsIncreasingEvent (rswRectangleCrossingEvent k l) :=
  isIncreasingEvent_squareBoundaryFreeRectangleCrossingEvent _ _

theorem measurableSet_rswSquareCrossingEvent (l : ℕ) :
    MeasurableSet (rswSquareCrossingEvent l) :=
  measurableSet_rswRectangleCrossingEvent 1 l

theorem isIncreasingEvent_rswSquareCrossingEvent (l : ℕ) :
    IsIncreasingEvent (rswSquareCrossingEvent l) :=
  isIncreasingEvent_rswRectangleCrossingEvent 1 l

theorem measurableSet_rswThreeHalvesCrossingEvent (l : ℕ) :
    MeasurableSet (rswThreeHalvesCrossingEvent l) :=
  measurableSet_squareBoundaryFreeRectangleCrossingEvent (3 * l) l

theorem isIncreasingEvent_rswThreeHalvesCrossingEvent (l : ℕ) :
    IsIncreasingEvent (rswThreeHalvesCrossingEvent l) :=
  isIncreasingEvent_squareBoundaryFreeRectangleCrossingEvent (3 * l) l

/-- The probability of `LR(kl,l)`. -/
noncomputable def rswRectangleCrossingProbability (p : I) (k l : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real (rswRectangleCrossingEvent k l)

/-- The probability of `LR(l)`. -/
noncomputable def rswSquareCrossingProbability (p : I) (l : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real (rswSquareCrossingEvent l)

/-- The probability of a boundary-free `3l × 2l` left-right crossing. -/
noncomputable def rswThreeHalvesCrossingProbability (p : I) (l : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real (rswThreeHalvesCrossingEvent l)

/-- `O(l)`: an open square-lattice cycle in `B(3l) \ B(l)` with odd face index at the
origin. -/
def rswAnnulusOpenCircuitEvent (l : ℕ) : Set (EdgeConfiguration 2) :=
  {omega | ∃ (x : SquareVertex) (c : squareGraph.Walk x x),
    c.IsCycle ∧ walkIsOpen omega c ∧
      (∀ z ∈ c.support,
        l < cubicLInfDist cubicOrigin z ∧
          cubicLInfDist cubicOrigin z ≤ 3 * l) ∧
      closedSquareWalkFaceParity c cubicOrigin = 1}

theorem dependsOn_rswAnnulusOpenCircuitEvent (l : ℕ) :
    DependsOn (cubicBoxEdges 2 cubicOrigin (3 * l))
      (rswAnnulusOpenCircuitEvent l) := by
  intro omega eta hagree
  constructor
  · rintro ⟨x, c, hcycle, hopen, hsupport, hparity⟩
    refine ⟨x, c, hcycle, ?_, hsupport, hparity⟩
    intro e he
    let ee : SquareEdge := ⟨e, c.edges_subset_edgeSet he⟩
    have heFinset : ee ∈ walkEdgeFinset c := (mem_walkEdgeFinset_iff c ee).mpr he
    have heBox : ee ∈ cubicBoxEdges 2 cubicOrigin (3 * l) :=
      walkEdgeFinset_subset_cubicBoxEdges_of_support c
        (fun z hz ↦ mem_cubicMetricBox_iff_lInfDist_le.mpr (hsupport z hz).2) heFinset
    exact (hagree ee heBox).mp (hopen e he)
  · rintro ⟨x, c, hcycle, hopen, hsupport, hparity⟩
    refine ⟨x, c, hcycle, ?_, hsupport, hparity⟩
    intro e he
    let ee : SquareEdge := ⟨e, c.edges_subset_edgeSet he⟩
    have heFinset : ee ∈ walkEdgeFinset c := (mem_walkEdgeFinset_iff c ee).mpr he
    have heBox : ee ∈ cubicBoxEdges 2 cubicOrigin (3 * l) :=
      walkEdgeFinset_subset_cubicBoxEdges_of_support c
        (fun z hz ↦ mem_cubicMetricBox_iff_lInfDist_le.mpr (hsupport z hz).2) heFinset
    exact (hagree ee heBox).mpr (hopen e he)

theorem measurableSet_rswAnnulusOpenCircuitEvent (l : ℕ) :
    MeasurableSet (rswAnnulusOpenCircuitEvent l) :=
  (dependsOn_rswAnnulusOpenCircuitEvent l).measurableSet

theorem isIncreasingEvent_rswAnnulusOpenCircuitEvent (l : ℕ) :
    IsIncreasingEvent (rswAnnulusOpenCircuitEvent l) := by
  intro omega eta hmono
  rintro ⟨x, c, hcycle, hopen, hsupport, hparity⟩
  exact ⟨x, c, hcycle,
    fun e he ↦ hmono (hopen e he), hsupport, hparity⟩

/-- The probability of the RSW annular circuit event. -/
noncomputable def rswAnnulusOpenCircuitProbability (p : I) (l : ℕ) : ℝ :=
  (bernoulliBondMeasure 2 p).real (rswAnnulusOpenCircuitEvent l)

end Percolation
