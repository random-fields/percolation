import Percolation.Planar.Crossings
import Percolation.Planar.Peierls
import Percolation.Planar.SquareStar

/-!
# Reachable frontier for planar site crossings

This file starts the deterministic crossing alternative needed for Grimmett's high-density site
estimate (7.70).  Given a site configuration in a finite square rectangle, it records the open
vertices reachable from the left side.  If there is no left--right crossing, the right side is
disjoint from this set.  Its internal vertex boundary is closed and separates every walk from
the reachable set to its complement.

The remaining planar step is to extract a top--bottom star-lattice path from this finite closed
separator.  Keeping the reachability and closure facts independent makes that geometric step
auditable without mixing it with probability estimates.
-/

namespace Percolation

/-- Open sites in the rectangle reachable from some open site on its left side. -/
noncomputable def siteRectangleLeftReachableVertices
    (m n : ℕ) (eta : Set SquareVertex) : Finset SquareVertex := by
  classical
  exact (squareRectangleVertices m n).filter fun y =>
    ∃ x : SquareVertex, x ∈ squareRectangleLeft m n ∧
      ∃ w : squareGraph.Walk x y,
        (∀ z ∈ w.support, z ∈ squareRectangleVertices m n) ∧
          ∀ z ∈ w.support, z ∈ eta

@[simp]
theorem mem_siteRectangleLeftReachableVertices_iff
    (m n : ℕ) (eta : Set SquareVertex) (y : SquareVertex) :
    y ∈ siteRectangleLeftReachableVertices m n eta ↔
      y ∈ squareRectangleVertices m n ∧
        ∃ x : SquareVertex, x ∈ squareRectangleLeft m n ∧
          ∃ w : squareGraph.Walk x y,
            (∀ z ∈ w.support, z ∈ squareRectangleVertices m n) ∧
              ∀ z ∈ w.support, z ∈ eta := by
  classical
  simp [siteRectangleLeftReachableVertices]

/-- An open left-side site is reachable by the nil walk. -/
theorem mem_siteRectangleLeftReachableVertices_of_mem_left
    {m n : ℕ} {eta : Set SquareVertex} {x : SquareVertex}
    (hxLeft : x ∈ squareRectangleLeft m n) (hxOpen : x ∈ eta) :
    x ∈ siteRectangleLeftReachableVertices m n eta := by
  rw [mem_siteRectangleLeftReachableVertices_iff]
  refine ⟨(Finset.mem_filter.mp hxLeft).1, x, hxLeft, SimpleGraph.Walk.nil, ?_, ?_⟩
  · intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    simpa [hz] using (Finset.mem_filter.mp hxLeft).1
  · intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    simpa [hz] using hxOpen

@[simp]
theorem siteRectangleLeftReachableVertices_empty (m n : ℕ) :
    siteRectangleLeftReachableVertices m n (∅ : Set SquareVertex) = ∅ := by
  ext y
  rw [mem_siteRectangleLeftReachableVertices_iff]
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨_hyRect, _x, _hxLeft, w, _hwRect, hwOpen⟩
  exact hwOpen y w.end_mem_support

/-- Reachability is closed under an adjacent open step which remains in the rectangle. -/
theorem siteRectangleLeftReachableVertices_step
    {m n : ℕ} {eta : Set SquareVertex} {x y : SquareVertex}
    (hx : x ∈ siteRectangleLeftReachableVertices m n eta)
    (hxy : squareGraph.Adj x y) (hyRect : y ∈ squareRectangleVertices m n)
    (hyOpen : y ∈ eta) :
    y ∈ siteRectangleLeftReachableVertices m n eta := by
  rw [mem_siteRectangleLeftReachableVertices_iff] at hx ⊢
  obtain ⟨hxRect, u, huLeft, w, hwRect, hwOpen⟩ := hx
  have hxOpen : x ∈ eta := hwOpen x (by simp)
  let step : squareGraph.Walk x y :=
    SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
  have hstepRect : ∀ z ∈ step.support, z ∈ squareRectangleVertices m n := by
    intro z hz
    simp only [step, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons] at hz
    rcases hz with rfl | (rfl | hz)
    · exact hxRect
    · exact hyRect
    · simp at hz
  have hstepOpen : ∀ z ∈ step.support, z ∈ eta := by
    intro z hz
    simp only [step, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons] at hz
    rcases hz with rfl | (rfl | hz)
    · exact hxOpen
    · exact hyOpen
    · simp at hz
  refine ⟨hyRect, u, huLeft, w.append step, ?_, ?_⟩
  · exact walk_append_support_subset hwRect hstepRect
  · exact walk_append_support_subset hwOpen hstepOpen

/-- The site crossing event occurs exactly when the left-reachable set meets the right side. -/
theorem mem_siteSquareRectangleCrossingEvent_iff_exists_mem_right_reachable
    (m n : ℕ) (eta : Set SquareVertex) :
    eta ∈ siteSquareRectangleCrossingEvent m n ↔
      ∃ y : SquareVertex, y ∈ squareRectangleRight m n ∧
        y ∈ siteRectangleLeftReachableVertices m n eta := by
  simp only [siteSquareRectangleCrossingEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hxLeft, y, hyRight, w, hwRect, hwOpen⟩
    refine ⟨y, hyRight, ?_⟩
    rw [mem_siteRectangleLeftReachableVertices_iff]
    exact ⟨(Finset.mem_filter.mp hyRight).1, x, hxLeft, w, hwRect, hwOpen⟩
  · rintro ⟨y, hyRight, hyReachable⟩
    rw [mem_siteRectangleLeftReachableVertices_iff] at hyReachable
    obtain ⟨_hyRect, x, hxLeft, w, hwRect, hwOpen⟩ := hyReachable
    exact ⟨x, hxLeft, y, hyRight, w, hwRect, hwOpen⟩

/-- Internal vertices immediately outside the left-reachable set. -/
noncomputable def siteRectangleLeftReachableBoundary
    (m n : ℕ) (eta : Set SquareVertex) : Finset SquareVertex := by
  classical
  exact (squareRectangleVertices m n).filter fun y =>
    y ∉ siteRectangleLeftReachableVertices m n eta ∧
      (y ∈ squareRectangleLeft m n ∨
        ∃ x ∈ siteRectangleLeftReachableVertices m n eta, squareGraph.Adj x y)

@[simp]
theorem mem_siteRectangleLeftReachableBoundary_iff
    (m n : ℕ) (eta : Set SquareVertex) (y : SquareVertex) :
    y ∈ siteRectangleLeftReachableBoundary m n eta ↔
      y ∈ squareRectangleVertices m n ∧
        y ∉ siteRectangleLeftReachableVertices m n eta ∧
          (y ∈ squareRectangleLeft m n ∨
            ∃ x ∈ siteRectangleLeftReachableVertices m n eta, squareGraph.Adj x y) := by
  classical
  simp [siteRectangleLeftReachableBoundary]

@[simp]
theorem siteRectangleLeftReachableBoundary_empty (m n : ℕ) :
    siteRectangleLeftReachableBoundary m n (∅ : Set SquareVertex) =
      squareRectangleLeft m n := by
  classical
  ext y
  simp [siteRectangleLeftReachableBoundary, squareRectangleLeft]

/-- Every internal boundary site is closed. -/
theorem not_mem_of_mem_siteRectangleLeftReachableBoundary
    {m n : ℕ} {eta : Set SquareVertex} {y : SquareVertex}
    (hy : y ∈ siteRectangleLeftReachableBoundary m n eta) : y ∉ eta := by
  rw [mem_siteRectangleLeftReachableBoundary_iff] at hy
  rintro hyOpen
  rcases hy.2.2 with hyLeft | ⟨x, hxReachable, hxy⟩
  · exact hy.2.1
      (mem_siteRectangleLeftReachableVertices_of_mem_left hyLeft hyOpen)
  · exact hy.2.1 (siteRectangleLeftReachableVertices_step
      hxReachable hxy hy.1 hyOpen)

/-- Every rectangle-confined walk from the reachable set to its complement visits the closed
internal boundary. -/
theorem exists_mem_siteRectangleLeftReachableBoundary_of_walk_leaves
    {m n : ℕ} {eta : Set SquareVertex} {u v : SquareVertex}
    (w : squareGraph.Walk u v)
    (hu : u ∈ siteRectangleLeftReachableVertices m n eta)
    (hv : v ∉ siteRectangleLeftReachableVertices m n eta)
    (hwRect : ∀ z ∈ w.support, z ∈ squareRectangleVertices m n) :
    ∃ y ∈ w.support, y ∈ siteRectangleLeftReachableBoundary m n eta := by
  obtain ⟨x, y, hx, hy, hxy, hxyEdge⟩ :=
    exists_boundary_edge_of_walk_leaves w hu hv
  refine ⟨y, w.mem_support_of_mem_edges hxyEdge (Sym2.mem_iff.mpr (Or.inr rfl)), ?_⟩
  rw [mem_siteRectangleLeftReachableBoundary_iff]
  refine ⟨hwRect y (w.mem_support_of_mem_edges hxyEdge
    (Sym2.mem_iff.mpr (Or.inr rfl))), hy, Or.inr ⟨x, hx, hxy⟩⟩

/-- On crossing failure, every rectangle-confined walk from the left side to the right side
visits the closed reachable boundary. -/
theorem exists_mem_siteRectangleLeftReachableBoundary_of_not_crossing
    {m n : ℕ} {eta : Set SquareVertex} {u v : SquareVertex}
    (hno : eta ∉ siteSquareRectangleCrossingEvent m n)
    (w : squareGraph.Walk u v)
    (huLeft : u ∈ squareRectangleLeft m n)
    (hvRight : v ∈ squareRectangleRight m n)
    (hwRect : ∀ z ∈ w.support, z ∈ squareRectangleVertices m n) :
    ∃ y ∈ w.support, y ∈ siteRectangleLeftReachableBoundary m n eta := by
  by_cases huReachable : u ∈ siteRectangleLeftReachableVertices m n eta
  · have hvNotReachable : v ∉ siteRectangleLeftReachableVertices m n eta := by
      intro hvReachable
      exact hno ((mem_siteSquareRectangleCrossingEvent_iff_exists_mem_right_reachable
        m n eta).mpr ⟨v, hvRight, hvReachable⟩)
    exact exists_mem_siteRectangleLeftReachableBoundary_of_walk_leaves
      w huReachable hvNotReachable hwRect
  · refine ⟨u, by simp, ?_⟩
    rw [mem_siteRectangleLeftReachableBoundary_iff]
    exact ⟨(Finset.mem_filter.mp huLeft).1, huReachable, Or.inl huLeft⟩

end Percolation
