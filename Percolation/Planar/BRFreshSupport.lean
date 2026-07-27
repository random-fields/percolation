import Percolation.Planar.BRReflection

/-!
# Fresh coordinate support for the Bollobás--Riordan extension

For a source square `[0,2n] × [-n,n]`, the doubled source rectangle is
`[0,m] × [-n,3n]`.  It is fixed by reflection across `y=n`.  The fresh extension support is the
boundary-free edge set of that rectangle with both the stopped exploration support and its
reflected copy removed.

This file only establishes coordinate locality.  The later first-contact argument proves that a
trimmed horizontal crossing can be witnessed inside this support.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

noncomputable section

/-- Translate the rectangle centered at height zero upward so that its center is `y=n`. -/
def brExtensionRectangleTranslateIso (n : ℕ) : squareGraph ≃g squareGraph :=
  squareCrossingTranslateIso cubicOrigin (squareVertex 0 (n : ℤ))

@[simp]
theorem brExtensionRectangleTranslateIso_zero (n : ℕ) (x : SquareVertex) :
    brExtensionRectangleTranslateIso n x 0 = x 0 := by
  simp [brExtensionRectangleTranslateIso, squareCrossingTranslateIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex]

@[simp]
theorem brExtensionRectangleTranslateIso_one (n : ℕ) (x : SquareVertex) :
    brExtensionRectangleTranslateIso n x 1 = x 1 + (n : ℤ) := by
  simp [brExtensionRectangleTranslateIso, squareCrossingTranslateIso,
    cubicTranslationIso_apply, cubicTranslate, cubicOrigin, squareVertex]

theorem brPrimalTopReflectionIso_extensionTranslate
    (n : ℕ) (x : SquareVertex) :
    brPrimalTopReflectionIso n (brExtensionRectangleTranslateIso n x) =
      brExtensionRectangleTranslateIso n (brHorizontalAxisReflectionIso x) := by
  ext i
  fin_cases i
  · simp
  · simp
    ring

theorem brPrimalTopReflectionIso_mapEdgeSet_extensionTranslate
    (n : ℕ) (e : SquareEdge) :
    (brPrimalTopReflectionIso n).mapEdgeSet
        ((brExtensionRectangleTranslateIso n).mapEdgeSet e) =
      (brExtensionRectangleTranslateIso n).mapEdgeSet
        (brHorizontalAxisReflectionIso.mapEdgeSet e) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
      apply Subtype.ext
      change s(brPrimalTopReflectionIso n
          (brExtensionRectangleTranslateIso n x),
        brPrimalTopReflectionIso n
          (brExtensionRectangleTranslateIso n y)) =
        s(brExtensionRectangleTranslateIso n
            (brHorizontalAxisReflectionIso x),
          brExtensionRectangleTranslateIso n
            (brHorizontalAxisReflectionIso y))
      rw [brPrimalTopReflectionIso_extensionTranslate,
        brPrimalTopReflectionIso_extensionTranslate]

/-- Boundary-free bonds in `[0,m] × [-n,3n]`. -/
def brExtensionRectangleEdges (m n : ℕ) : Finset SquareEdge :=
  (squareBoundaryFreeRectangleEdges m (2 * n)).map
    (brExtensionRectangleTranslateIso n).mapEdgeSet.toEmbedding

/-- Reflection across `y=n` preserves the exact doubled-rectangle coordinate support. -/
theorem brPrimalTopReflectionIso_image_extensionRectangleEdges
    (m n : ℕ) :
    (brExtensionRectangleEdges m n).image
        (brPrimalTopReflectionIso n).mapEdgeSet =
      brExtensionRectangleEdges m n := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [brExtensionRectangleEdges, Finset.mem_map] at hf ⊢
    obtain ⟨g, hg, rfl⟩ := hf
    have hreflect : brHorizontalAxisReflectionIso.mapEdgeSet g ∈
        squareBoundaryFreeRectangleEdges m (2 * n) := by
      rw [← brHorizontalAxisReflectionIso_image_boundaryFreeRectangleEdges]
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    exact ⟨brHorizontalAxisReflectionIso.mapEdgeSet g, hreflect,
      (brPrimalTopReflectionIso_mapEdgeSet_extensionTranslate n g).symm⟩
  · rw [Finset.card_image_of_injective _
      (brPrimalTopReflectionIso n).mapEdgeSet.injective]

/-- The reflected copy of the finite coordinate support exposed by a stopped fiber. -/
def brReflectedReachableFaceFiberSupport
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset SquareEdge :=
  (brReachableFaceFiberSupport n R).map
    (brPrimalTopReflectionIso n).mapEdgeSet.toEmbedding

/-- The symmetric set of exposed coordinates: the original fiber support and its reflection. -/
def brSymmetricReachableFaceFiberSupport
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset SquareEdge :=
  brReachableFaceFiberSupport n R ∪ brReflectedReachableFaceFiberSupport n R

@[simp]
theorem mem_brReflectedReachableFaceFiberSupport_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {e : SquareEdge} :
    e ∈ brReflectedReachableFaceFiberSupport n R ↔
      (brPrimalTopReflectionIso n).mapEdgeSet e ∈
        brReachableFaceFiberSupport n R := by
  rw [brReflectedReachableFaceFiberSupport, Finset.mem_map]
  constructor
  · rintro ⟨f, hf, hfe⟩
    subst e
    change (brPrimalTopReflectionIso n).mapEdgeSet
        ((brPrimalTopReflectionIso n).mapEdgeSet f) ∈
      brReachableFaceFiberSupport n R
    simpa only [brPrimalTopReflectionIso_mapEdgeSet_involutive] using hf
  · intro he
    refine ⟨(brPrimalTopReflectionIso n).mapEdgeSet e, he, ?_⟩
    change (brPrimalTopReflectionIso n).mapEdgeSet
        ((brPrimalTopReflectionIso n).mapEdgeSet e) = e
    exact brPrimalTopReflectionIso_mapEdgeSet_involutive n e

@[simp]
theorem brPrimalTopReflectionIso_mem_symmetricFiberSupport_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)} {e : SquareEdge} :
    (brPrimalTopReflectionIso n).mapEdgeSet e ∈
        brSymmetricReachableFaceFiberSupport n R ↔
      e ∈ brSymmetricReachableFaceFiberSupport n R := by
  simp only [brSymmetricReachableFaceFiberSupport, Finset.mem_union,
    mem_brReflectedReachableFaceFiberSupport_iff,
    brPrimalTopReflectionIso_mapEdgeSet_involutive]
  exact or_comm

/-- Genuinely fresh bonds available to extend a selected stopped boundary to the right. -/
def brFreshExtensionEdges
    (m n : ℕ) (R : Finset (BRLeftmostDualVertex n)) : Finset SquareEdge :=
  brExtensionRectangleEdges m n \ brSymmetricReachableFaceFiberSupport n R

/-- Reflection across the top of the source square preserves the fresh coordinate set. -/
theorem brPrimalTopReflectionIso_image_freshExtensionEdges
    (m n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    (brFreshExtensionEdges m n R).image
        (brPrimalTopReflectionIso n).mapEdgeSet =
      brFreshExtensionEdges m n R := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [brFreshExtensionEdges, Finset.mem_sdiff] at hf ⊢
    refine ⟨?_, ?_⟩
    · rw [← brPrimalTopReflectionIso_image_extensionRectangleEdges m n]
      exact Finset.mem_image.mpr ⟨f, hf.1, rfl⟩
    · rw [brPrimalTopReflectionIso_mem_symmetricFiberSupport_iff]
      exact hf.2
  · rw [Finset.card_image_of_injective _
      (brPrimalTopReflectionIso n).mapEdgeSet.injective]

theorem brFreshExtensionEdges_subset_extensionRectangleEdges
    (m n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    brFreshExtensionEdges m n R ⊆ brExtensionRectangleEdges m n := by
  intro e he
  exact (Finset.mem_sdiff.mp he).1

/-- The extension coordinates are disjoint from every coordinate queried by the stopped fiber. -/
theorem disjoint_brReachableFaceFiberSupport_brFreshExtensionEdges
    (m n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brReachableFaceFiberSupport n R) (brFreshExtensionEdges m n R) := by
  rw [Finset.disjoint_left]
  intro e heFiber heFresh
  exact (Finset.mem_sdiff.mp heFresh).2
    (Finset.mem_union_left _ heFiber)

/-- The fresh support is also disjoint from the reflected exposed coordinates. -/
theorem disjoint_brReflectedReachableFaceFiberSupport_brFreshExtensionEdges
    (m n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Disjoint (brReflectedReachableFaceFiberSupport n R)
      (brFreshExtensionEdges m n R) := by
  rw [Finset.disjoint_left]
  intro e heFiber heFresh
  exact (Finset.mem_sdiff.mp heFresh).2
    (Finset.mem_union_right _ heFiber)

/-- Horizontal crossing of the doubled rectangle, expressed by transporting the repository's
boundary-free event from its centered normalization. -/
def brExtensionRectangleCrossingEvent (m n : ℕ) : Set (EdgeConfiguration 2) :=
  cubicGraphIsoEvent (brExtensionRectangleTranslateIso n)
    (squareBoundaryFreeRectangleCrossingEvent m (2 * n))

theorem dependsOn_brExtensionRectangleCrossingEvent (m n : ℕ) :
    DependsOn (brExtensionRectangleEdges m n)
      (brExtensionRectangleCrossingEvent m n) := by
  intro omega eta hagree
  apply dependsOn_squareBoundaryFreeRectangleCrossingEvent m (2 * n)
  intro e he
  apply hagree
  rw [brExtensionRectangleEdges, Finset.mem_map]
  exact ⟨e, he, rfl⟩

theorem measurableSet_brExtensionRectangleCrossingEvent (m n : ℕ) :
    MeasurableSet (brExtensionRectangleCrossingEvent m n) :=
  measurableSet_cubicGraphIsoEvent _
    (measurableSet_squareBoundaryFreeRectangleCrossingEvent m (2 * n))

theorem isIncreasingEvent_brExtensionRectangleCrossingEvent (m n : ℕ) :
    IsIncreasingEvent (brExtensionRectangleCrossingEvent m n) :=
  isIncreasingEvent_cubicGraphIsoEvent _
    (isIncreasingEvent_squareBoundaryFreeRectangleCrossingEvent m (2 * n))

theorem bernoulliBondMeasure_real_brExtensionRectangleCrossingEvent
    (p : I) (m n : ℕ) :
    (bernoulliBondMeasure 2 p).real (brExtensionRectangleCrossingEvent m n) =
      (bernoulliBondMeasure 2 p).real
        (squareBoundaryFreeRectangleCrossingEvent m (2 * n)) :=
  bernoulliBondMeasure_real_cubicGraphIsoEvent p _
    (measurableSet_squareBoundaryFreeRectangleCrossingEvent m (2 * n))

end

end Percolation
