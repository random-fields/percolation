import Percolation.Planar.BRFiberGeometry
import Percolation.Planar.BRResolvedBoundary
import Percolation.Planar.BRSelectedCrossing

/-!
# Filled outer hull of a stopped BR exploration

The exact reached-face set may have finite complementary holes.  Those holes are responsible for
the irrelevant boundary cycles which make an arbitrary parity-selected boundary component
unsuitable for a stopping argument.  This module fills every complementary component not joined
to the right exterior column.  Its first API proves the key outer-boundary fact: every frame edge
leaving the filled hull already leaves the original reached set.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- Frame edges whose two endpoints avoid the original reached-face set. -/
def brComplementEdgeConfiguration
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Set (Sym2 (BRLeftmostDualVertex n)) :=
  {e | ∀ z ∈ e, z ∉ R}

@[simp]
theorem mem_brComplementEdgeConfiguration_mk
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {x y : BRLeftmostDualVertex n} :
    s(x, y) ∈ brComplementEdgeConfiguration n R ↔ x ∉ R ∧ y ∉ R := by
  change (∀ z : BRLeftmostDualVertex n, z ∈ s(x, y) → z ∉ R) ↔ _
  constructor
  · intro h
    exact ⟨h x (by simp), h y (by simp)⟩
  · rintro ⟨hx, hy⟩ z hz
    rw [Sym2.mem_iff] at hz
    exact hz.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)

/-- Faces connected to the right exterior column without entering `R`. -/
def brRightComplementReachableFaces
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset (BRLeftmostDualVertex n) :=
  finiteGraphReachableVertices (brLeftmostDualGraph n) (brRightmostDualTargets n)
    (brComplementEdgeConfiguration n R)

/-- The reached set with every complementary component cut off from the right exterior filled
in. -/
def brFilledReachableHull
    (n : ℕ) (R : Finset (BRLeftmostDualVertex n)) :
    Finset (BRLeftmostDualVertex n) :=
  Finset.univ \ brRightComplementReachableFaces n R

/-- Enlarging the forbidden reached set can only shrink the component connected to the right
exterior. -/
theorem brRightComplementReachableFaces_anti
    {n : ℕ} {R S : Finset (BRLeftmostDualVertex n)}
    (hRS : R ⊆ S) :
    brRightComplementReachableFaces n S ⊆
      brRightComplementReachableFaces n R := by
  intro x hx
  rw [brRightComplementReachableFaces,
    mem_finiteGraphReachableVertices_iff] at hx ⊢
  rcases hx with ⟨r, hr, w, hw⟩
  refine ⟨r, hr, w, ?_⟩
  intro e he z hz
  exact fun hzR ↦ hw e he z hz (hRS hzR)

/-- Filling complementary holes is monotone in the underlying reached-face set. -/
theorem brFilledReachableHull_mono
    {n : ℕ} {R S : Finset (BRLeftmostDualVertex n)}
    (hRS : R ⊆ S) :
    brFilledReachableHull n R ⊆ brFilledReachableHull n S := by
  intro x hx
  rw [brFilledReachableHull, Finset.mem_sdiff] at hx ⊢
  exact ⟨Finset.mem_univ x,
    fun hxRightS ↦ hx.2 (brRightComplementReachableFaces_anti hRS hxRightS)⟩

/-- The face in the right exterior column at the same height as `x`. -/
def brRightTargetAtSameHeight
    (n : ℕ) (x : BRLeftmostDualVertex n) : BRLeftmostDualVertex n :=
  ⟨Function.update x.1 (0 : Fin 2) (2 * (n : ℤ)), by
    rw [mem_brLeftmostDualFaces_iff]
    have hx := mem_brLeftmostDualFaces_iff.mp x.2
    simp [Function.update]
    omega⟩

@[simp]
theorem brRightTargetAtSameHeight_mem_targets
    (n : ℕ) (x : BRLeftmostDualVertex n) :
    brRightTargetAtSameHeight n x ∈ brRightmostDualTargets n := by
  rw [mem_brRightmostDualTargets_iff]
  simp [brRightTargetAtSameHeight]

/-- The horizontal frame walk from a face to the right exterior column. -/
def brHorizontalWalkToRightTarget
    (n : ℕ) (x : BRLeftmostDualVertex n) :
    (brLeftmostDualGraph n).Walk x (brRightTargetAtSameHeight n x) := by
  let k := Int.toNat (2 * (n : ℤ) - x.1 0)
  have hk0 : 0 ≤ 2 * (n : ℤ) - x.1 0 := by
    have hx := mem_brLeftmostDualFaces_iff.mp x.2
    omega
  have hk : (k : ℤ) = 2 * (n : ℤ) - x.1 0 := by
    exact Int.toNat_of_nonneg hk0
  let raw := cubicWalkFrom x.1 (List.replicate k ((0 : Fin 2), true))
  have hend : cubicEndpointFrom x.1
      (List.replicate k ((0 : Fin 2), true)) =
      (brRightTargetAtSameHeight n x).1 := by
    rw [cubicEndpointFrom_replicate_pos]
    ext i
    fin_cases i
    · simp [brRightTargetAtSameHeight, hk]
    · simp [brRightTargetAtSameHeight]
  let w : dualSquareGraph.Walk x.1 (brRightTargetAtSameHeight n x).1 :=
    raw.copy rfl hend
  have hwFrame : ∀ z ∈ w.support, z ∈ brLeftmostDualFaces n := by
    intro z hz
    have hzRaw : z ∈ cubicVerticesFrom x.1
        (List.replicate k ((0 : Fin 2), true)) := by
      simpa [w, raw, SimpleGraph.Walk.support_copy, cubicWalkFrom_support] using hz
    have hz0 := cubicVerticesFrom_replicate_pos_coord_between
      x.1 (0 : Fin 2) k hzRaw
    have hz1 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      x.1 (0 : Fin 2) (1 : Fin 2) k (by decide) hzRaw
    rw [mem_brLeftmostDualFaces_iff]
    have hx := mem_brLeftmostDualFaces_iff.mp x.2
    simp only [hk] at hz0
    omega
  let q := w.induce (brLeftmostDualFaces n : Set DualSquareVertex) hwFrame
  exact q.copy (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)

/-- The canonical horizontal walk to the right target stays on the starting row and moves only
to the right. -/
theorem brHorizontalWalkToRightTarget_support_coordinates
    (n : ℕ) (x : BRLeftmostDualVertex n) {z : BRLeftmostDualVertex n}
    (hz : z ∈ (brHorizontalWalkToRightTarget n x).support) :
    x.1 0 ≤ z.1 0 ∧ z.1 0 ≤ 2 * (n : ℤ) ∧ z.1 1 = x.1 1 := by
  let k := Int.toNat (2 * (n : ℤ) - x.1 0)
  have hk0 : 0 ≤ 2 * (n : ℤ) - x.1 0 := by
    have hx := mem_brLeftmostDualFaces_iff.mp x.2
    omega
  have hk : (k : ℤ) = 2 * (n : ℤ) - x.1 0 :=
    Int.toNat_of_nonneg hk0
  let raw := cubicWalkFrom x.1 (List.replicate k ((0 : Fin 2), true))
  have hend : cubicEndpointFrom x.1
      (List.replicate k ((0 : Fin 2), true)) =
      (brRightTargetAtSameHeight n x).1 := by
    rw [cubicEndpointFrom_replicate_pos]
    ext i
    fin_cases i
    · simp [brRightTargetAtSameHeight, hk]
    · simp [brRightTargetAtSameHeight]
  let w : dualSquareGraph.Walk x.1 (brRightTargetAtSameHeight n x).1 :=
    raw.copy rfl hend
  have hwFrame : ∀ y ∈ w.support, y ∈ brLeftmostDualFaces n := by
    intro y hy
    have hyRaw : y ∈ cubicVerticesFrom x.1
        (List.replicate k ((0 : Fin 2), true)) := by
      simpa [w, raw, SimpleGraph.Walk.support_copy,
        cubicWalkFrom_support] using hy
    have hy0 := cubicVerticesFrom_replicate_pos_coord_between
      x.1 (0 : Fin 2) k hyRaw
    have hy1 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
      x.1 (0 : Fin 2) (1 : Fin 2) k (by decide) hyRaw
    rw [mem_brLeftmostDualFaces_iff]
    have hx := mem_brLeftmostDualFaces_iff.mp x.2
    simp only [hk] at hy0
    omega
  let q := w.induce (brLeftmostDualFaces n : Set DualSquareVertex) hwFrame
  have hzQ : z ∈ q.support := by
    simpa [brHorizontalWalkToRightTarget, k, raw, w, q] using hz
  have hzMap : z.1 ∈
      (q.map (brLeftmostDualToAmbientHom n)).support := by
    simp only [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzQ, rfl⟩
  have hqMap : q.map (brLeftmostDualToAmbientHom n) = w := by
    change (w.induce (brLeftmostDualFaces n : Set DualSquareVertex) hwFrame).map
      (brLeftmostDualToAmbientHom n) = w
    exact SimpleGraph.Walk.map_induce _ _
  have hzW : z.1 ∈ w.support := by
    rw [hqMap] at hzMap
    exact hzMap
  have hzRaw : z.1 ∈ cubicVerticesFrom x.1
      (List.replicate k ((0 : Fin 2), true)) := by
    simpa [w, raw, SimpleGraph.Walk.support_copy,
      cubicWalkFrom_support] using hzW
  have hz0 := cubicVerticesFrom_replicate_pos_coord_between
    x.1 (0 : Fin 2) k hzRaw
  have hz1 := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
    x.1 (0 : Fin 2) (1 : Fin 2) k (by decide) hzRaw
  simp only [hk] at hz0
  omega

/-- Frame edges whose two endpoints lie in a prescribed hull. -/
def brHullInternalEdgeConfiguration
    (n : ℕ) (H : Finset (BRLeftmostDualVertex n)) :
    Set (Sym2 (BRLeftmostDualVertex n)) :=
  {e | ∀ z ∈ e, z ∈ H}

@[simp]
theorem mem_brHullInternalEdgeConfiguration_mk
    {n : ℕ} {H : Finset (BRLeftmostDualVertex n)}
    {x y : BRLeftmostDualVertex n} :
    s(x, y) ∈ brHullInternalEdgeConfiguration n H ↔ x ∈ H ∧ y ∈ H := by
  change (∀ z : BRLeftmostDualVertex n, z ∈ s(x, y) → z ∈ H) ↔ _
  constructor
  · intro h
    exact ⟨h x (by simp), h y (by simp)⟩
  · rintro ⟨hx, hy⟩ z hz
    rw [Sym2.mem_iff] at hz
    exact hz.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)

@[simp]
theorem brReachedDualFace_subtype_iff
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {z : BRLeftmostDualVertex n} :
    brReachedDualFace n R z.1 ↔ z ∈ R := by
  simp [brReachedDualFace, brReachedFaceCoordinates,
    brLeftmostDualVertexValEmbedding]

private theorem brComplementOpenWalk_end_not_mem
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {x y : BRLeftmostDualVertex n}
    (w : (brLeftmostDualGraph n).Walk x y)
    (hx : x ∉ R)
    (hw : finiteGraphWalkIsOpen (brComplementEdgeConfiguration n R) w) :
    y ∉ R := by
  induction w with
  | nil => exact hx
  | @cons x z y hxz q ih =>
      have hopen : s(x, z) ∈ brComplementEdgeConfiguration n R :=
        hw _ (by simp)
      have hz : z ∉ R :=
        (mem_brComplementEdgeConfiguration_mk.mp hopen).2
      apply ih hz
      intro e he
      exact hw e (by simp [he])

/-- A set avoiding the right target column is contained in its filled hull. -/
theorem subset_brFilledReachableHull
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hRright : Disjoint R (brRightmostDualTargets n)) :
    R ⊆ brFilledReachableHull n R := by
  intro z hzR
  rw [brFilledReachableHull, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ z, ?_⟩
  rw [brRightComplementReachableFaces,
    mem_finiteGraphReachableVertices_iff]
  rintro ⟨r, hrTarget, w, hw⟩
  have hrNotR : r ∉ R := by
    intro hrR
    exact Finset.disjoint_left.mp hRright hrR hrTarget
  exact (brComplementOpenWalk_end_not_mem w hrNotR hw) hzR

/-- Every right target lies outside the filled hull. -/
theorem disjoint_brFilledReachableHull_rightTargets
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hRright : Disjoint R (brRightmostDualTargets n)) :
    Disjoint (brFilledReachableHull n R) (brRightmostDualTargets n) := by
  rw [Finset.disjoint_left]
  intro z hzHull hzTarget
  have hzNotR : z ∉ R := by
    intro hzR
    exact Finset.disjoint_left.mp hRright hzR hzTarget
  have hzOutside : z ∈ brRightComplementReachableFaces n R := by
    rw [brRightComplementReachableFaces,
      mem_finiteGraphReachableVertices_iff]
    exact finiteGraphReachableFrom_source hzTarget
  exact (Finset.mem_sdiff.mp hzHull).2 hzOutside

/-- A separating reached set has a separating filled hull. -/
theorem BRSeparatingReachedSet.filledHull
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRSeparatingReachedSet n R) :
    BRSeparatingReachedSet n (brFilledReachableHull n R) := by
  refine ⟨hR.1.trans (subset_brFilledReachableHull hR.2), ?_⟩
  exact disjoint_brFilledReachableHull_rightTargets hR.2

/-- A face in the original reached set has a source walk all of whose edges stay in the filled
hull. -/
private theorem exists_open_brHullInternalWalk_of_mem_reached
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (hRright : Disjoint R (brRightmostDualTargets n))
    {x : BRLeftmostDualVertex n} (hx : x ∈ R) :
    ∃ a ∈ brLeftmostDualSources n,
      ∃ w : (brLeftmostDualGraph n).Walk a x,
        finiteGraphWalkIsOpen
          (brHullInternalEdgeConfiguration n (brFilledReachableHull n R)) w := by
  have hxReach : x ∈ brLeftReachableFaces n omega := by
    change brLeftReachableFaces n omega = R at homega
    simpa [homega] using hx
  rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff] at hxReach
  rcases hxReach with ⟨a, ha, w, hwOpen⟩
  refine ⟨a, ha, w, ?_⟩
  intro e he z hz
  apply subset_brFilledReachableHull hRright
  change brLeftReachableFaces n omega = R at homega
  rw [← homega, brLeftReachableFaces,
    mem_finiteGraphReachableVertices_iff]
  refine ⟨a, ha, w.takeUntil z ?_, ?_⟩
  · exact w.mem_support_of_mem_edges he hz
  · intro f hf
    exact hwOpen f (w.edges_takeUntil_subset _ hf)

/-- Complement reachability is closed under a frame step which stays outside `R`. -/
theorem mem_brRightComplementReachableFaces_of_adj
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {x y : BRLeftmostDualVertex n}
    (hRright : Disjoint R (brRightmostDualTargets n))
    (hy : y ∈ brRightComplementReachableFaces n R)
    (hxR : x ∉ R)
    (hxy : (brLeftmostDualGraph n).Adj x y) :
    x ∈ brRightComplementReachableFaces n R := by
  rw [brRightComplementReachableFaces,
    mem_finiteGraphReachableVertices_iff] at hy ⊢
  rcases hy with ⟨r, hr, w, hw⟩
  have hrNotR : r ∉ R := by
    intro hrR
    exact Finset.disjoint_left.mp hRright hrR hr
  have hyNotR : y ∉ R := brComplementOpenWalk_end_not_mem w hrNotR hw
  apply finiteGraphReachableFrom_step ⟨r, hr, w, hw⟩ hxy.symm
  exact mem_brComplementEdgeConfiguration_mk.mpr ⟨hyNotR, hxR⟩

/-- The inside endpoint of an edge leaving the filled hull belongs to the original reached set.
This removes all finite-hole boundary components from the stopping geometry. -/
theorem mem_of_mem_filledHull_of_adj_of_not_mem_filledHull
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {x y : BRLeftmostDualVertex n}
    (hRright : Disjoint R (brRightmostDualTargets n))
    (hx : x ∈ brFilledReachableHull n R)
    (hy : y ∉ brFilledReachableHull n R)
    (hxy : (brLeftmostDualGraph n).Adj x y) :
    x ∈ R := by
  by_contra hxR
  have hyOutside : y ∈ brRightComplementReachableFaces n R := by
    rw [brFilledReachableHull, Finset.mem_sdiff] at hy
    simpa using hy
  have hxOutside :=
    mem_brRightComplementReachableFaces_of_adj hRright hyOutside hxR hxy
  exact (Finset.mem_sdiff.mp hx).2 hxOutside

/-- Every filled-hull face outside the original reached set is joined inside the hull to an
original reached face.  The proof follows the horizontal line to the right exterior and reads
the last outside-to-inside transition in the reversed walk. -/
private theorem exists_open_brHullInternalWalk_from_reached
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hRright : Disjoint R (brRightmostDualTargets n))
    {x : BRLeftmostDualVertex n}
    (hxHull : x ∈ brFilledReachableHull n R) :
    ∃ r ∈ R, ∃ w : (brLeftmostDualGraph n).Walk r x,
      finiteGraphWalkIsOpen
        (brHullInternalEdgeConfiguration n (brFilledReachableHull n R)) w := by
  let t := brRightTargetAtSameHeight n x
  let p := brHorizontalWalkToRightTarget n x
  have htTarget : t ∈ brRightmostDualTargets n :=
    brRightTargetAtSameHeight_mem_targets n x
  have htOutside : t ∉ brFilledReachableHull n R := by
    exact fun htHull ↦
      Finset.disjoint_left.mp
        (disjoint_brFilledReachableHull_rightTargets hRright) htHull htTarget
  have houtsideMem : ∃ z, z ∈ p.reverse.support ∧
      z ∉ brFilledReachableHull n R := by
    exact ⟨t, by simp [p, t], htOutside⟩
  have hendInside : ¬(x ∉ brFilledReachableHull n R) := by
    simpa using hxHull
  obtain ⟨u, huOutside, q, _hqSub, hqTail⟩ :=
    exists_isSubwalk_suffix_from_last_region p.reverse houtsideMem hendInside
  cases q with
  | nil =>
      exact (huOutside hxHull).elim
  | @cons u v y huv q =>
      have hvHull : v ∈ brFilledReachableHull n R := by
        by_contra hv
        exact hqTail v (by simp) hv
      have hvR : v ∈ R :=
        mem_of_mem_filledHull_of_adj_of_not_mem_filledHull
          hRright hvHull huOutside huv.symm
      refine ⟨v, hvR, q, ?_⟩
      intro e he z hz
      by_contra hzHull
      apply hqTail z
      · have hzq : z ∈ q.support := q.mem_support_of_mem_edges he hz
        simpa using hzq
      · exact hzHull

/-- Every face of the filled hull is joined to the left source column by a frame walk which
stays wholly inside the filled hull. -/
theorem exists_brHullInternalWalk_from_source
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R)
    {x : BRLeftmostDualVertex n}
    (hxHull : x ∈ brFilledReachableHull n R) :
    ∃ a ∈ brLeftmostDualSources n,
      ∃ w : (brLeftmostDualGraph n).Walk a x,
        finiteGraphWalkIsOpen
          (brHullInternalEdgeConfiguration n (brFilledReachableHull n R)) w := by
  rcases hR.1 with ⟨omega, homega⟩
  by_cases hxR : x ∈ R
  · exact exists_open_brHullInternalWalk_of_mem_reached
      homega hR.2 hxR
  · rcases exists_open_brHullInternalWalk_from_reached hR.2 hxHull with
      ⟨r, hrR, q, hq⟩
    rcases exists_open_brHullInternalWalk_of_mem_reached
        homega hR.2 hrR with ⟨a, ha, w, hw⟩
    refine ⟨a, ha, w.append q, ?_⟩
    intro e he
    rw [SimpleGraph.Walk.edges_append] at he
    rcases List.mem_append.mp he with he | he
    · exact hw e he
    · exact hq e he

/-- Every face outside the filled hull is joined to the right exterior column by a frame walk
which stays wholly outside the filled hull. -/
theorem exists_brRightComplementWalk_from_target
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {x : BRLeftmostDualVertex n}
    (hxOutside : x ∉ brFilledReachableHull n R) :
    ∃ r ∈ brRightmostDualTargets n,
      ∃ w : (brLeftmostDualGraph n).Walk r x,
        ∀ z ∈ w.support, z ∉ brFilledReachableHull n R := by
  have hxReach : x ∈ brRightComplementReachableFaces n R := by
    rw [brFilledReachableHull, Finset.mem_sdiff] at hxOutside
    simpa using hxOutside
  rw [brRightComplementReachableFaces,
    mem_finiteGraphReachableVertices_iff] at hxReach
  rcases hxReach with ⟨r, hr, w, hw⟩
  refine ⟨r, hr, w, ?_⟩
  intro z hz hzHull
  have hzReach : z ∈ brRightComplementReachableFaces n R := by
    rw [brRightComplementReachableFaces,
      mem_finiteGraphReachableVertices_iff]
    refine ⟨r, hr, w.takeUntil z hz, ?_⟩
    intro e he
    exact hw e (w.edges_takeUntil_subset hz he)
  exact (Finset.mem_sdiff.mp hzHull).2 hzReach

/-- The primal bond crossed by an edge of the finite dual frame. -/
def brFrameCrossedPrimalEdge
    (n : ℕ) (d : (brLeftmostDualGraph n).edgeSet) : SquareEdge :=
  squareEdgeDualCrossingEquiv.symm (brLeftmostDualEdgeEmbedding n d)

theorem brFrameCrossedPrimalEdge_injective (n : ℕ) :
    Function.Injective (brFrameCrossedPrimalEdge n) := by
  intro d e hde
  apply (brLeftmostDualEdgeEmbedding n).injective
  apply squareEdgeDualCrossingEquiv.symm.injective
  exact hde

/-- A primal configuration realizing the internal adjacency of a filled hull: precisely the
frame bonds crossing a non-internal hull edge are declared open. -/
def brFilledHullPrimalConfiguration
    (n : ℕ) (H : Finset (BRLeftmostDualVertex n)) : EdgeConfiguration 2 :=
  {e | ∃ d : (brLeftmostDualGraph n).edgeSet,
    brFrameCrossedPrimalEdge n d = e ∧
      d.1 ∉ brHullInternalEdgeConfiguration n H}

private theorem brFrameCrossedPrimalEdge_not_mem_filledHullConfiguration_of_internal
    {n : ℕ} {H : Finset (BRLeftmostDualVertex n)}
    (d : (brLeftmostDualGraph n).edgeSet)
    (hd : d.1 ∈ brHullInternalEdgeConfiguration n H) :
    brFrameCrossedPrimalEdge n d ∉ brFilledHullPrimalConfiguration n H := by
  rintro ⟨e, heq, heNotInternal⟩
  have hed : e = d := brFrameCrossedPrimalEdge_injective n heq
  subst e
  exact heNotInternal hd

private theorem mem_brClosedDualExplorationConfiguration_filledHull_of_internal
    {n : ℕ} {H : Finset (BRLeftmostDualVertex n)}
    {e : Sym2 (BRLeftmostDualVertex n)}
    (he : e ∈ (brLeftmostDualGraph n).edgeSet)
    (hInternal : e ∈ brHullInternalEdgeConfiguration n H) :
    e ∈ brClosedDualExplorationConfiguration n
      (brFilledHullPrimalConfiguration n H) := by
  rw [mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet he]
  by_cases hallowed : brFrameCrossedPrimalEdge n ⟨e, he⟩ ∈
      squareBoundaryFreeRectangleEdges (2 * n) n
  · exact Or.inr
      (brFrameCrossedPrimalEdge_not_mem_filledHullConfiguration_of_internal
        ⟨e, he⟩ hInternal)
  · exact Or.inl hallowed

/-- Every cut edge of the filled hull is an original reached/unreached cut, hence crosses an
allowed open primal bond on the realized fiber. -/
theorem brFilledHullCutCrossedPrimalEdge_mem_boundaryFree_and_configuration
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} {x y : BRLeftmostDualVertex n}
    (homega : omega ∈ brReachableFaceFiber n R)
    (hRright : Disjoint R (brRightmostDualTargets n))
    (hx : x ∈ brFilledReachableHull n R)
    (hy : y ∉ brFilledReachableHull n R)
    (hxy : (brLeftmostDualGraph n).Adj x y) :
    let crossed := squareEdgeDualCrossingEquiv.symm
      (brLeftmostDualEdgeEmbedding n
        ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩)
    crossed ∈ squareBoundaryFreeRectangleEdges (2 * n) n ∧ crossed ∈ omega := by
  have hxR : x ∈ R :=
    mem_of_mem_filledHull_of_adj_of_not_mem_filledHull hRright hx hy hxy
  have hyR : y ∉ R := by
    intro hyR
    exact hy (subset_brFilledReachableHull hRright hyR)
  have hxReach : x ∈ brLeftReachableFaces n omega := by
    change brLeftReachableFaces n omega = R at homega
    simpa [homega] using hxR
  have hyReach : y ∉ brLeftReachableFaces n omega := by
    change brLeftReachableFaces n omega = R at homega
    simpa [homega] using hyR
  exact brCutCrossedPrimalEdge_mem_boundaryFree_and_configuration
    hxReach hyReach hxy

/-- A frame edge leaving the filled hull is closed in the dual exploration associated with the
canonical filled-hull primal configuration. -/
private theorem not_mem_brClosedDualExplorationConfiguration_filledHull_of_cut
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (hRright : Disjoint R (brRightmostDualTargets n))
    {x y : BRLeftmostDualVertex n}
    (hx : x ∈ brFilledReachableHull n R)
    (hy : y ∉ brFilledReachableHull n R)
    (hxy : (brLeftmostDualGraph n).Adj x y) :
    s(x, y) ∉ brClosedDualExplorationConfiguration n
      (brFilledHullPrimalConfiguration n (brFilledReachableHull n R)) := by
  let d : (brLeftmostDualGraph n).edgeSet :=
    ⟨s(x, y), (brLeftmostDualGraph n).mem_edgeSet.mpr hxy⟩
  have hcut := brFilledHullCutCrossedPrimalEdge_mem_boundaryFree_and_configuration
    homega hRright hx hy hxy
  have hallowed : brFrameCrossedPrimalEdge n d ∈
      squareBoundaryFreeRectangleEdges (2 * n) n := by
    exact hcut.1
  have hnotInternal : d.1 ∉ brHullInternalEdgeConfiguration n
      (brFilledReachableHull n R) := by
    rw [mem_brHullInternalEdgeConfiguration_mk]
    exact fun h ↦ hy h.2
  have hopen : brFrameCrossedPrimalEdge n d ∈
      brFilledHullPrimalConfiguration n (brFilledReachableHull n R) :=
    ⟨d, rfl, hnotInternal⟩
  rw [mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet d.2]
  simp only [not_or, not_not]
  exact ⟨hallowed, hopen⟩

/-- Every walk internal to the filled hull is open in its canonical realizing exploration. -/
private theorem finiteGraphWalkIsOpen_filledHullPrimalConfiguration_of_internal
    {n : ℕ} {H : Finset (BRLeftmostDualVertex n)}
    {x y : BRLeftmostDualVertex n}
    (w : (brLeftmostDualGraph n).Walk x y)
    (hw : finiteGraphWalkIsOpen (brHullInternalEdgeConfiguration n H) w) :
    finiteGraphWalkIsOpen
      (brClosedDualExplorationConfiguration n
        (brFilledHullPrimalConfiguration n H)) w := by
  intro e he
  apply mem_brClosedDualExplorationConfiguration_filledHull_of_internal
    (w.edges_subset_edgeSet he)
  exact hw e he

/-- An exploration-open walk in the canonical realizing configuration cannot leave the filled
hull. -/
private theorem walk_end_mem_filledHull_of_start_mem_of_isOpen
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (hRright : Disjoint R (brRightmostDualTargets n))
    {x y : BRLeftmostDualVertex n}
    (w : (brLeftmostDualGraph n).Walk x y)
    (hx : x ∈ brFilledReachableHull n R)
    (hw : finiteGraphWalkIsOpen
      (brClosedDualExplorationConfiguration n
        (brFilledHullPrimalConfiguration n (brFilledReachableHull n R))) w) :
    y ∈ brFilledReachableHull n R := by
  induction w with
  | nil => exact hx
  | @cons x z y hxz q ih =>
      have hzHull : z ∈ brFilledReachableHull n R := by
        by_contra hzHull
        exact (not_mem_brClosedDualExplorationConfiguration_filledHull_of_cut
          homega hRright hx hzHull hxz) (hw _ (by simp))
      apply ih hzHull
      intro e he
      exact hw e (by simp [he])

/-- Filling complementary holes preserves realizability as a stopped exploration fiber. -/
theorem BRAdmissibleSeparatingFiber.filledHull
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hR : BRAdmissibleSeparatingFiber n R) :
    BRAdmissibleSeparatingFiber n (brFilledReachableHull n R) := by
  rcases hR.1 with ⟨omega, homega⟩
  let H := brFilledReachableHull n R
  let eta := brFilledHullPrimalConfiguration n H
  refine ⟨⟨eta, ?_⟩, disjoint_brFilledReachableHull_rightTargets hR.2⟩
  change brLeftReachableFaces n eta = H
  apply Finset.Subset.antisymm
  · intro x hxReach
    rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff] at hxReach
    rcases hxReach with ⟨a, ha, w, hw⟩
    have haR : a ∈ R :=
      hR.separatingReachedSet.1 ha
    have haH : a ∈ H := subset_brFilledReachableHull hR.2 haR
    exact walk_end_mem_filledHull_of_start_mem_of_isOpen
      homega hR.2 w haH hw
  · intro x hxH
    rw [brLeftReachableFaces, mem_finiteGraphReachableVertices_iff]
    by_cases hxR : x ∈ R
    · rcases exists_open_brHullInternalWalk_of_mem_reached
          homega hR.2 hxR with ⟨a, ha, w, hw⟩
      exact ⟨a, ha, w,
        finiteGraphWalkIsOpen_filledHullPrimalConfiguration_of_internal w hw⟩
    · rcases exists_open_brHullInternalWalk_from_reached hR.2 hxH with
        ⟨r, hrR, q, hq⟩
      rcases exists_open_brHullInternalWalk_of_mem_reached
          homega hR.2 hrR with ⟨a, ha, w, hw⟩
      refine ⟨a, ha, w.append q, ?_⟩
      apply finiteGraphWalkIsOpen_filledHullPrimalConfiguration_of_internal
      intro e he
      rw [SimpleGraph.Walk.edges_append] at he
      rcases List.mem_append.mp he with he | he
      · exact hw e he
      · exact hq e he

/-- A stopped-boundary edge of the filled hull whose endpoints lie in the exploration frame is
also a stopped-boundary edge of the original reached set. -/
theorem brStoppedDualBoundaryEdge_filledHull_imp_reached
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hRright : Disjoint R (brRightmostDualTargets n))
    {d : DualSquarePositiveEdge}
    (hbase : d.base ∈ brLeftmostDualFaces n)
    (hstep : cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n)
    (hd : brStoppedDualBoundaryEdge n (brFilledReachableHull n R) d) :
    brStoppedDualBoundaryEdge n R d := by
  let x : BRLeftmostDualVertex n := ⟨d.base, hbase⟩
  let y : BRLeftmostDualVertex n :=
    ⟨cubicStepFrom d.base (d.axis, true), hstep⟩
  have hxy : (brLeftmostDualGraph n).Adj x y := by
    change dualSquareGraph.Adj d.base
      (cubicStepFrom d.base (d.axis, true))
    exact cubicGraph_adj_stepFrom d.base (d.axis, true)
  have hbaseHull : brReachedDualFace n (brFilledReachableHull n R) d.base ↔
      x ∈ brFilledReachableHull n R := by
    simpa [x] using
      (brReachedDualFace_subtype_iff
        (R := brFilledReachableHull n R) (z := x))
  have hstepHull : brReachedDualFace n (brFilledReachableHull n R)
      (cubicStepFrom d.base (d.axis, true)) ↔
      y ∈ brFilledReachableHull n R := by
    simpa [y] using
      (brReachedDualFace_subtype_iff
        (R := brFilledReachableHull n R) (z := y))
  have hchange : ¬(x ∈ brFilledReachableHull n R ↔
      y ∈ brFilledReachableHull n R) := by
    rw [brStoppedDualBoundaryEdge, hbaseHull, hstepHull] at hd
    exact hd
  have hbaseR : brReachedDualFace n R d.base ↔ x ∈ R := by
    simpa [x] using (brReachedDualFace_subtype_iff (R := R) (z := x))
  have hstepR : brReachedDualFace n R
      (cubicStepFrom d.base (d.axis, true)) ↔ y ∈ R := by
    simpa [y] using (brReachedDualFace_subtype_iff (R := R) (z := y))
  rw [brStoppedDualBoundaryEdge, hbaseR, hstepR]
  by_cases hx : x ∈ brFilledReachableHull n R
  · have hy : y ∉ brFilledReachableHull n R := fun hy ↦ hchange ⟨fun _ ↦ hy, fun _ ↦ hx⟩
    have hxR := mem_of_mem_filledHull_of_adj_of_not_mem_filledHull
      hRright hx hy hxy
    have hyR : y ∉ R := fun hyR ↦ hy (subset_brFilledReachableHull hRright hyR)
    exact fun hiff ↦ hyR (hiff.mp hxR)
  · have hy : y ∈ brFilledReachableHull n R := by
      by_contra hy
      exact hchange ⟨fun hx' ↦ (hx hx').elim, fun hy' ↦ (hy hy').elim⟩
    have hyR := mem_of_mem_filledHull_of_adj_of_not_mem_filledHull
      hRright hy hx hxy.symm
    have hxR : x ∉ R := fun hxR ↦ hx (subset_brFilledReachableHull hRright hxR)
    exact fun hiff ↦ hxR (hiff.mpr hyR)

set_option maxHeartbeats 800000 in
/-- Every retained primal interface edge selected from the filled hull is open in every
configuration realizing the original reached-face fiber.  Thus filling holes changes only the
deterministic selector; it does not manufacture any open primal bond. -/
theorem brTruncatedInterfacePrimalEdge_filledHull_mem_configuration_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R)
    (hRright : Disjoint R (brRightmostDualTargets n))
    (d : BRTruncatedInterfaceEdge n (brFilledReachableHull n R)) :
    brTruncatedInterfacePrimalEdge d ∈ omega := by
  have hd := mem_brTruncatedDualBoundaryPositiveEdges_iff.mp d.2
  have hdRBoundary : brStoppedDualBoundaryEdge n R d.1 :=
    brStoppedDualBoundaryEdge_filledHull_imp_reached hRright
      hd.2.1 hd.2.2.1 hd.1
  let dR : BRTruncatedInterfaceEdge n R :=
    ⟨d.1, mem_brTruncatedDualBoundaryPositiveEdges_iff.mpr
      ⟨hdRBoundary, hd.2.1, hd.2.2.1, hd.2.2.2⟩⟩
  have hopen :=
    brTruncatedInterfacePrimalEdge_mem_configuration_of_mem_fiber
      homega (mem_brTruncatedInterfacePrimalEdges_iff.mpr
        ⟨dR, rfl⟩)
  exact hopen

/-- The selected bottom--top primal interface of the filled hull is open in every
configuration in the original stopped fiber. -/
theorem walkIsOpen_brSelectedPrimalWalk_filledHull_of_mem_fiber
    {n : ℕ} {R : Finset (BRLeftmostDualVertex n)}
    (hn : 0 < n) (hR : BRAdmissibleSeparatingFiber n R)
    {omega : EdgeConfiguration 2} (homega : omega ∈ brReachableFaceFiber n R) :
    walkIsOpen omega
      (brSelectedPrimalWalk hn hR.filledHull) := by
  intro e he
  let f : SquareEdge :=
    ⟨e, (brSelectedPrimalWalk hn hR.filledHull).edges_subset_edgeSet he⟩
  have hfWalk : f ∈ walkEdgeFinset (brSelectedPrimalWalk hn hR.filledHull) :=
    (mem_walkEdgeFinset_iff (brSelectedPrimalWalk hn hR.filledHull) f).mpr he
  have hfInterface : f ∈
      brTruncatedInterfacePrimalEdges n (brFilledReachableHull n R) :=
    walkEdgeFinset_brSelectedPrimalWalk_subset_interface hn hR.filledHull hfWalk
  rcases mem_brTruncatedInterfacePrimalEdges_iff.mp hfInterface with ⟨d, hd⟩
  have hopen : brTruncatedInterfacePrimalEdge d ∈ omega :=
    brTruncatedInterfacePrimalEdge_filledHull_mem_configuration_of_mem_fiber
      homega hR.2 d
  have hfOpen : f ∈ omega := hd ▸ hopen
  exact hfOpen

end

end Percolation
