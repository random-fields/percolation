import Percolation.Planar.BRResolvedBoundary
import Percolation.Planar.RSWPlacements

/-!
# Reflections used by the Bollobás--Riordan crossing extension

The source proof reflects a square crossing across its top side.  Primal vertices are reflected
across the line `y = n`, while dual face coordinates are reflected across the line
`y = n - 1/2`.  Keeping these as separate graph automorphisms avoids a hidden off-by-one in the
stopped-dual barrier.
-/

namespace Percolation

noncomputable section

/-- Reflection across the horizontal axis. -/
def brHorizontalAxisReflectionIso : squareGraph ≃g squareGraph :=
  cubicCoordinateReflectionIso (1 : Fin 2)

@[simp]
theorem brHorizontalAxisReflectionIso_zero (x : SquareVertex) :
    brHorizontalAxisReflectionIso x 0 = x 0 := by
  simp [brHorizontalAxisReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv]

@[simp]
theorem brHorizontalAxisReflectionIso_one (x : SquareVertex) :
    brHorizontalAxisReflectionIso x 1 = -x 1 := by
  simp [brHorizontalAxisReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv]

theorem brHorizontalAxisReflectionIso_mem_rectangle_iff
    (m h : ℕ) (x : SquareVertex) :
    brHorizontalAxisReflectionIso x ∈ squareRectangleVertices m h ↔
      x ∈ squareRectangleVertices m h := by
  rw [mem_squareRectangleVertices_iff, mem_squareRectangleVertices_iff]
  simp only [brHorizontalAxisReflectionIso_zero,
    brHorizontalAxisReflectionIso_one]
  omega

theorem brHorizontalAxisReflectionIso_boundary_iff
    (m h : ℕ) (x : SquareVertex) :
    squareRectangleBoundaryVertex m h (brHorizontalAxisReflectionIso x) ↔
      squareRectangleBoundaryVertex m h x := by
  simp only [squareRectangleBoundaryVertex,
    brHorizontalAxisReflectionIso_zero, brHorizontalAxisReflectionIso_one]
  omega

/-- Reflection in the horizontal axis preserves any centered boundary-free rectangle support. -/
theorem brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges
    (m h : ℕ) :
    (squareBoundaryFreeRectangleEdges m h).image
        brHorizontalAxisReflectionIso.mapEdgeSet =
      squareBoundaryFreeRectangleEdges m h := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at hf ⊢
    refine ⟨?_, ?_⟩
    · rw [squareRectangleEdges, Finset.mem_filter]
      have hmapped : ∀ z ∈
          (brHorizontalAxisReflectionIso.mapEdgeSet f : Sym2 SquareVertex),
          z ∈ squareRectangleVertices m h := by
        intro z hz
        change z ∈ Sym2.map brHorizontalAxisReflectionIso
          (f : Sym2 SquareVertex) at hz
        rw [Sym2.mem_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [brHorizontalAxisReflectionIso_mem_rectangle_iff]
        exact endpoint_mem_squareRectangle_of_edge_mem hf.1 hw
      refine ⟨mem_cubicBoxEdges_of_endpoints ?_,
        hmapped _ (Sym2.out_fst_mem _), hmapped _ (Sym2.out_snd_mem _)⟩
      intro z hz
      exact mem_cubicMetricBox_max_of_mem_squareRectangleVertices (hmapped z hz)
    · intro hboundary
      apply hf.2
      have hmappedBoundary : ∀ z ∈
          (brHorizontalAxisReflectionIso.mapEdgeSet f : Sym2 SquareVertex),
          squareRectangleBoundaryVertex m h z := by
        intro z hz
        rw [← (brHorizontalAxisReflectionIso.mapEdgeSet f).1.out_eq,
          Sym2.mem_iff] at hz
        exact hz.elim (fun hz ↦ hz ▸ hboundary.1)
          (fun hz ↦ hz ▸ hboundary.2)
      have hsourceBoundary : ∀ z ∈ (f : Sym2 SquareVertex),
          squareRectangleBoundaryVertex m h z := by
        intro z hz
        rw [← brHorizontalAxisReflectionIso_boundary_iff m h z]
        apply hmappedBoundary (brHorizontalAxisReflectionIso z)
        exact Sym2.mem_map.mpr ⟨z, hz, rfl⟩
      exact ⟨hsourceBoundary f.1.out.1 (Sym2.out_fst_mem _),
        hsourceBoundary f.1.out.2 (Sym2.out_snd_mem _)⟩
  · rw [Finset.card_image_of_injective _
      brHorizontalAxisReflectionIso.mapEdgeSet.injective]

/-- Reflection of primal vertices across the horizontal line `y = n`. -/
def brPrimalTopReflectionIso (n : ℕ) : squareGraph ≃g squareGraph :=
  (cubicCoordinateReflectionIso (1 : Fin 2)).trans
    (cubicTranslationIso cubicOrigin (squareVertex 0 (2 * (n : ℤ))))

/-- Reflection of primal vertices across the vertical line `x = n`, the horizontal symmetry
used to place the second copy of the source `X(R)` event. -/
def brPrimalSourceVerticalAxisReflectionIso (n : ℕ) : squareGraph ≃g squareGraph :=
  (cubicCoordinateReflectionIso (0 : Fin 2)).trans
    (cubicTranslationIso cubicOrigin (squareVertex (2 * (n : ℤ)) 0))

/-- Reflection of dual face coordinates across the horizontal line `y = n - 1/2`.
Thus row `j` is sent to row `2n - 1 - j`. -/
def brDualTopReflectionIso (n : ℕ) : dualSquareGraph ≃g dualSquareGraph :=
  (cubicCoordinateReflectionIso (1 : Fin 2)).trans
    (cubicTranslationIso cubicOrigin
      (squareVertex 0 (2 * (n : ℤ) - 1)))

@[simp]
theorem brPrimalTopReflectionIso_zero (n : ℕ) (x : SquareVertex) :
    brPrimalTopReflectionIso n x 0 = x 0 := by
  simp [brPrimalTopReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]

@[simp]
theorem brPrimalTopReflectionIso_one (n : ℕ) (x : SquareVertex) :
    brPrimalTopReflectionIso n x 1 = 2 * (n : ℤ) - x 1 := by
  simp [brPrimalTopReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]
  ring

@[simp]
theorem brPrimalSourceVerticalAxisReflectionIso_zero
    (n : ℕ) (x : SquareVertex) :
    brPrimalSourceVerticalAxisReflectionIso n x 0 = 2 * (n : ℤ) - x 0 := by
  simp [brPrimalSourceVerticalAxisReflectionIso,
    cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex]
  ring

@[simp]
theorem brPrimalSourceVerticalAxisReflectionIso_one
    (n : ℕ) (x : SquareVertex) :
    brPrimalSourceVerticalAxisReflectionIso n x 1 = x 1 := by
  simp [brPrimalSourceVerticalAxisReflectionIso,
    cubicCoordinateReflectionIso, cubicCoordinateReflectionEquiv,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex]

@[simp]
theorem brDualTopReflectionIso_zero (n : ℕ) (z : DualSquareVertex) :
    brDualTopReflectionIso n z 0 = z 0 := by
  simp [brDualTopReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]

@[simp]
theorem brDualTopReflectionIso_one (n : ℕ) (z : DualSquareVertex) :
    brDualTopReflectionIso n z 1 = 2 * (n : ℤ) - 1 - z 1 := by
  simp [brDualTopReflectionIso, cubicCoordinateReflectionIso,
    cubicCoordinateReflectionEquiv, cubicTranslationIso_apply,
    cubicTranslate, cubicOrigin, squareVertex]
  ring

theorem brPrimalTopReflectionIso_involutive (n : ℕ) (x : SquareVertex) :
    brPrimalTopReflectionIso n (brPrimalTopReflectionIso n x) = x := by
  ext i
  fin_cases i
  · simp
  · simp

theorem brPrimalSourceVerticalAxisReflectionIso_involutive
    (n : ℕ) (x : SquareVertex) :
    brPrimalSourceVerticalAxisReflectionIso n
        (brPrimalSourceVerticalAxisReflectionIso n x) = x := by
  ext i
  fin_cases i
  · simp
  · simp

theorem brDualTopReflectionIso_involutive (n : ℕ) (z : DualSquareVertex) :
    brDualTopReflectionIso n (brDualTopReflectionIso n z) = z := by
  ext i
  fin_cases i
  · simp
  · simp

theorem brPrimalTopReflectionIso_symm (n : ℕ) :
    (brPrimalTopReflectionIso n).symm = brPrimalTopReflectionIso n := by
  apply RelIso.ext
  intro x
  apply (brPrimalTopReflectionIso n).injective
  rw [RelIso.apply_symm_apply]
  exact (brPrimalTopReflectionIso_involutive n x).symm

theorem brPrimalSourceVerticalAxisReflectionIso_symm (n : ℕ) :
    (brPrimalSourceVerticalAxisReflectionIso n).symm =
      brPrimalSourceVerticalAxisReflectionIso n := by
  apply RelIso.ext
  intro x
  apply (brPrimalSourceVerticalAxisReflectionIso n).injective
  rw [RelIso.apply_symm_apply]
  exact (brPrimalSourceVerticalAxisReflectionIso_involutive n x).symm

theorem brDualTopReflectionIso_symm (n : ℕ) :
    (brDualTopReflectionIso n).symm = brDualTopReflectionIso n := by
  apply RelIso.ext
  intro z
  apply (brDualTopReflectionIso n).injective
  rw [RelIso.apply_symm_apply]
  exact (brDualTopReflectionIso_involutive n z).symm

theorem brPrimalTopReflectionIso_mapEdgeSet_involutive
    (n : ℕ) (e : SquareEdge) :
    (brPrimalTopReflectionIso n).mapEdgeSet
        ((brPrimalTopReflectionIso n).mapEdgeSet e) = e := by
  have hmap : (brPrimalTopReflectionIso n).symm.mapEdgeSet =
      (brPrimalTopReflectionIso n).mapEdgeSet.symm := by
    ext f
    rfl
  calc
    (brPrimalTopReflectionIso n).mapEdgeSet
        ((brPrimalTopReflectionIso n).mapEdgeSet e) =
      (brPrimalTopReflectionIso n).symm.mapEdgeSet
        ((brPrimalTopReflectionIso n).mapEdgeSet e) := by
          rw [brPrimalTopReflectionIso_symm]
    _ = (brPrimalTopReflectionIso n).mapEdgeSet.symm
        ((brPrimalTopReflectionIso n).mapEdgeSet e) := by rw [hmap]
    _ = e := (brPrimalTopReflectionIso n).mapEdgeSet.symm_apply_apply e

theorem brPrimalSourceVerticalAxisReflectionIso_mapEdgeSet_involutive
    (n : ℕ) (e : SquareEdge) :
    (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet
        ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e) = e := by
  have hmap : (brPrimalSourceVerticalAxisReflectionIso n).symm.mapEdgeSet =
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet.symm := by
    ext f
    rfl
  calc
    (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet
        ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e) =
      (brPrimalSourceVerticalAxisReflectionIso n).symm.mapEdgeSet
        ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e) := by
          rw [brPrimalSourceVerticalAxisReflectionIso_symm]
    _ = (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet.symm
        ((brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet e) := by rw [hmap]
    _ = e :=
      (brPrimalSourceVerticalAxisReflectionIso n).mapEdgeSet.symm_apply_apply e

theorem brDualTopReflectionIso_mapEdgeSet_involutive
    (n : ℕ) (e : DualSquareEdge) :
    (brDualTopReflectionIso n).mapEdgeSet
        ((brDualTopReflectionIso n).mapEdgeSet e) = e := by
  have hmap : (brDualTopReflectionIso n).symm.mapEdgeSet =
      (brDualTopReflectionIso n).mapEdgeSet.symm := by
    ext f
    rfl
  calc
    (brDualTopReflectionIso n).mapEdgeSet
        ((brDualTopReflectionIso n).mapEdgeSet e) =
      (brDualTopReflectionIso n).symm.mapEdgeSet
        ((brDualTopReflectionIso n).mapEdgeSet e) := by
          rw [brDualTopReflectionIso_symm]
    _ = (brDualTopReflectionIso n).mapEdgeSet.symm
        ((brDualTopReflectionIso n).mapEdgeSet e) := by rw [hmap]
    _ = e := (brDualTopReflectionIso n).mapEdgeSet.symm_apply_apply e

/-- The reflected copy of the reached faces, in ambient dual coordinates. -/
def brReflectedReachedFaceCoordinates
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset DualSquareVertex :=
  (brReachedFaceCoordinates n R).map
    (brDualTopReflectionIso n).toEquiv.toEmbedding

/-- The symmetric stopped barrier used by the extension argument. -/
def brSymmetricBarrierFaceCoordinates
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset DualSquareVertex :=
  brReachedFaceCoordinates n R ∪ brReflectedReachedFaceCoordinates n R

@[simp]
theorem mem_brReflectedReachedFaceCoordinates_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {z : DualSquareVertex} :
    z ∈ brReflectedReachedFaceCoordinates n R ↔
      brDualTopReflectionIso n z ∈ brReachedFaceCoordinates n R := by
  rw [brReflectedReachedFaceCoordinates, Finset.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    subst z
    change brDualTopReflectionIso n (brDualTopReflectionIso n w) ∈
      brReachedFaceCoordinates n R
    simpa only [brDualTopReflectionIso_involutive] using hw
  · intro hz
    refine ⟨brDualTopReflectionIso n z, hz, ?_⟩
    change brDualTopReflectionIso n (brDualTopReflectionIso n z) = z
    exact brDualTopReflectionIso_involutive n z

@[simp]
theorem mem_brSymmetricBarrierFaceCoordinates_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {z : DualSquareVertex} :
    z ∈ brSymmetricBarrierFaceCoordinates n R ↔
      z ∈ brReachedFaceCoordinates n R ∨
        brDualTopReflectionIso n z ∈ brReachedFaceCoordinates n R := by
  simp [brSymmetricBarrierFaceCoordinates]

/-- Reflection preserves the symmetric barrier face set. -/
theorem brDualTopReflectionIso_mem_symmetricBarrier_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {z : DualSquareVertex} :
    brDualTopReflectionIso n z ∈ brSymmetricBarrierFaceCoordinates n R ↔
      z ∈ brSymmetricBarrierFaceCoordinates n R := by
  simp only [mem_brSymmetricBarrierFaceCoordinates_iff,
    brDualTopReflectionIso_involutive]
  exact or_comm

end

end Percolation
