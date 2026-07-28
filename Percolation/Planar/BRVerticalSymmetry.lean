import Percolation.Planar.BRVerticalEvents
import Percolation.Planar.RSWPlacements

/-!
# Symmetry of the vertical BR square crossing

The stopped BR exploration produces a bottom-to-top crossing of the centered square.  This
module identifies that event with the quarter-turned RSW square crossing and transfers its
Bernoulli probability without an informal appeal to rotational symmetry.
-/

namespace Percolation

open MeasureTheory
open scoped unitInterval

noncomputable section

/-- The coordinate swap about the centre of `[0,2n] × [-n,n]`. -/
def brSquareQuarterTurnIso (n : ℕ) : squareGraph ≃g squareGraph :=
  squareCrossingQuarterTurnIso (rswRectangleCenter 1 n) (rswRectangleCenter 1 n)

@[simp]
theorem brSquareQuarterTurnIso_zero (n : ℕ) (x : SquareVertex) :
    brSquareQuarterTurnIso n x 0 = x 1 + n := by
  simp [brSquareQuarterTurnIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]

@[simp]
theorem brSquareQuarterTurnIso_one (n : ℕ) (x : SquareVertex) :
    brSquareQuarterTurnIso n x 1 = x 0 - n := by
  simp [brSquareQuarterTurnIso, squareCrossingQuarterTurnIso, rswRectangleCenter,
    squareCoordinateSwap, cubicTranslationIso_apply, cubicTranslate,
    cubicCoordinatePermutationIso, cubicCoordinatePermutationEquiv, squareVertex, cubicOrigin]
  ring

@[simp]
theorem brSquareQuarterTurnIso_involutive (n : ℕ) (x : SquareVertex) :
    brSquareQuarterTurnIso n (brSquareQuarterTurnIso n x) = x := by
  ext i
  fin_cases i <;> simp

theorem brSquareQuarterTurnIso_mem_rectangle_iff
    (n : ℕ) (x : SquareVertex) :
    brSquareQuarterTurnIso n x ∈ squareRectangleVertices (2 * n) n ↔
      x ∈ squareRectangleVertices (2 * n) n := by
  rw [mem_squareRectangleVertices_iff, mem_squareRectangleVertices_iff]
  simp only [brSquareQuarterTurnIso_zero, brSquareQuarterTurnIso_one]
  omega

theorem brSquareQuarterTurnIso_boundary_iff
    (n : ℕ) (x : SquareVertex) :
    squareRectangleBoundaryVertex (2 * n) n (brSquareQuarterTurnIso n x) ↔
      squareRectangleBoundaryVertex (2 * n) n x := by
  simp only [squareRectangleBoundaryVertex, brSquareQuarterTurnIso_zero,
    brSquareQuarterTurnIso_one]
  omega

/-- The centred quarter-turn preserves the exact boundary-free square edge support. -/
theorem brSquareQuarterTurnIso_image_boundaryFreeRectangleEdges (n : ℕ) :
    (squareBoundaryFreeRectangleEdges (2 * n) n).image
        (brSquareQuarterTurnIso n).mapEdgeSet =
      squareBoundaryFreeRectangleEdges (2 * n) n := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hf ⊢
    refine ⟨?_, ?_⟩
    · rw [squareRectangleEdges, Finset.mem_filter]
      have hmapped : ∀ z ∈
          ((brSquareQuarterTurnIso n).mapEdgeSet f : Sym2 SquareVertex),
          z ∈ squareRectangleVertices (2 * n) n := by
        intro z hz
        change z ∈ Sym2.map (brSquareQuarterTurnIso n) (f : Sym2 SquareVertex) at hz
        rw [Sym2.mem_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [brSquareQuarterTurnIso_mem_rectangle_iff]
        exact endpoint_mem_squareRectangle_of_edge_mem hf.1 hw
      refine ⟨mem_cubicBoxEdges_of_endpoints ?_,
        hmapped _ (Sym2.out_fst_mem _), hmapped _ (Sym2.out_snd_mem _)⟩
      intro z hz
      exact mem_cubicMetricBox_max_of_mem_squareRectangleVertices (hmapped z hz)
    · intro hboundary
      apply hf.2
      have hmappedBoundary : ∀ z ∈
          ((brSquareQuarterTurnIso n).mapEdgeSet f : Sym2 SquareVertex),
          squareRectangleBoundaryVertex (2 * n) n z := by
        intro z hz
        rw [← ((brSquareQuarterTurnIso n).mapEdgeSet f).1.out_eq,
          Sym2.mem_iff] at hz
        exact hz.elim (fun h ↦ h ▸ hboundary.1) (fun h ↦ h ▸ hboundary.2)
      have hsourceBoundary : ∀ z ∈ (f : Sym2 SquareVertex),
          squareRectangleBoundaryVertex (2 * n) n z := by
        intro z hz
        rw [← brSquareQuarterTurnIso_boundary_iff n z]
        apply hmappedBoundary (brSquareQuarterTurnIso n z)
        exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
      exact ⟨hsourceBoundary f.1.out.1 (Sym2.out_fst_mem _),
        hsourceBoundary f.1.out.2 (Sym2.out_snd_mem _)⟩
  · rw [Finset.card_image_of_injective _ (brSquareQuarterTurnIso n).mapEdgeSet.injective]

theorem brSquareQuarterTurnIso_mem_left_iff_mem_bottom
    (n : ℕ) (x : SquareVertex) :
    x ∈ squareRectangleLeft (2 * n) n ↔
      brSquareQuarterTurnIso n x ∈ brSquareBottomSide n := by
  rw [mem_squareRectangleLeft_iff, mem_brSquareBottomSide_iff]
  simp only [brSquareQuarterTurnIso_zero, brSquareQuarterTurnIso_one]
  omega

theorem brSquareQuarterTurnIso_mem_right_iff_mem_top
    (n : ℕ) (x : SquareVertex) :
    x ∈ squareRectangleRight (2 * n) n ↔
      brSquareQuarterTurnIso n x ∈ brSquareTopSide n := by
  rw [mem_squareRectangleRight_iff, mem_brSquareTopSide_iff]
  simp only [brSquareQuarterTurnIso_zero, brSquareQuarterTurnIso_one]
  omega

/-- The literal BR vertical crossing is the quarter-turned RSW square crossing. -/
theorem rswVerticalPlacementEvent_square_eq_brSquareVerticalCrossingEvent (n : ℕ) :
    rswVerticalPlacementEvent (rswRectangleCenter 1 n) (rswRectangleCenter 1 n)
        (rswSquareCrossingEvent n) =
      brSquareVerticalCrossingEvent n := by
  let F := brSquareQuarterTurnIso n
  have hF : squareCrossingQuarterTurnIso
      (rswRectangleCenter 1 n) (rswRectangleCenter 1 n) = F := rfl
  ext omega
  simp only [rswVerticalPlacementEvent, cubicGraphIsoEvent, Set.mem_preimage,
    rswSquareCrossingEvent, rswRectangleCrossingEvent,
    squareBoundaryFreeRectangleCrossingEvent, brSquareVerticalCrossingEvent,
    Set.mem_iUnion]
  rw [hF]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hxy' :=
      (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (squareBoundaryFreeRectangleEdges (2 * n) n) omega x y).mp hxy
    rw [brSquareQuarterTurnIso_image_boundaryFreeRectangleEdges] at hxy'
    exact ⟨F x, (brSquareQuarterTurnIso_mem_left_iff_mem_bottom n x).mp hx,
      F y, (brSquareQuarterTurnIso_mem_right_iff_mem_top n y).mp hy, hxy'⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨F x, ?_, F y, ?_, ?_⟩
    · apply (brSquareQuarterTurnIso_mem_left_iff_mem_bottom n (F x)).mpr
      simpa [F] using hx
    · apply (brSquareQuarterTurnIso_mem_right_iff_mem_top n (F y)).mpr
      simpa [F] using hy
    · apply (cubicGraphIsoConfigurationPullback_mem_connectionEventIn_iff F
        (squareBoundaryFreeRectangleEdges (2 * n) n) omega (F x) (F y)).mpr
      rw [brSquareQuarterTurnIso_image_boundaryFreeRectangleEdges]
      simpa [F] using hxy

/-- Vertical and horizontal boundary-free square crossings have the same Bernoulli probability. -/
theorem bernoulliBondMeasure_real_brSquareVerticalCrossingEvent
    (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (brSquareVerticalCrossingEvent n) =
      rswSquareCrossingProbability p n := by
  rw [← rswVerticalPlacementEvent_square_eq_brSquareVerticalCrossingEvent]
  exact bernoulliBondMeasure_real_rswVerticalPlacementEvent p
    (rswRectangleCenter 1 n) (rswRectangleCenter 1 n)
    (measurableSet_rswSquareCrossingEvent n)

end

end Percolation
