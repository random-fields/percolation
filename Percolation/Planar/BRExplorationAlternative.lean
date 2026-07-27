import Percolation.Planar.AlternatingPaths
import Percolation.Planar.BRVerticalEvents

/-!
# Deterministic alternative for the BR stopped exploration

This file develops the finite mod-two intersection argument needed to show that a boundary-free
bottom-to-top primal crossing excludes an exploration-open dual connection from the left source
column to the right target column.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- Moving one dual face to the right preserves the horizontal-ray count of a closed primal walk
unless the dual step's crossed primal bond occurs in that walk. -/
private theorem closedWalk_horizontalRayCount_stepRight_eq_of_crossed_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o) (f : DualSquareVertex)
    (hnot : (dualToPrimalCrossingPositiveEdge
      (⟨f, (0 : Fin 2)⟩ : DualSquarePositiveEdge)).toEdge ∉ walkEdgeFinset c) :
    c.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) =
      c.edges.countP (squareEdgeCrossesFaceHorizontalRayBool
        (cubicStepFrom f ((0 : Fin 2), true))) := by
  classical
  apply List.countP_congr
  intro e he
  have hne : e ≠
      ((dualToPrimalCrossingPositiveEdge
        (⟨f, (0 : Fin 2)⟩ : DualSquarePositiveEdge)).toEdge : Sym2 SquareVertex) := by
    intro heq
    apply hnot
    rw [mem_walkEdgeFinset_iff]
    simpa [heq] using he
  induction e using Sym2.ind with
  | _ u v =>
      have huv : squareGraph.Adj u v := c.adj_of_mem_edges he
      rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨i, rfl⟩
      rcases i with ⟨i, b⟩
      fin_cases i <;> cases b <;>
        simp [squareEdgeCrossesFaceHorizontalRayBool,
          squareEdgeCrossesFaceHorizontalRay,
          dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
          squarePerp, cubicStepFrom, cubicDirectionIncrement] at hne ⊢ <;>
        try omega
      all_goals
        intro hy
        by_cases hu : u 0 = f 0 + 1
        · exfalso
          simp [funext_iff, hu, hy] at hne
          try omega
        · omega

/-- Moving one dual face upward preserves the vertical-ray count of a closed primal walk unless
the dual step's crossed primal bond occurs in that walk. -/
private theorem closedWalk_verticalRayCount_stepUp_eq_of_crossed_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o) (f : DualSquareVertex)
    (hnot : (dualToPrimalCrossingPositiveEdge
      (⟨f, (1 : Fin 2)⟩ : DualSquarePositiveEdge)).toEdge ∉ walkEdgeFinset c) :
    c.edges.countP (squareEdgeCrossesFaceVerticalRayBool f) =
      c.edges.countP (squareEdgeCrossesFaceVerticalRayBool
        (cubicStepFrom f ((1 : Fin 2), true))) := by
  classical
  apply List.countP_congr
  intro e he
  have hne : e ≠
      ((dualToPrimalCrossingPositiveEdge
        (⟨f, (1 : Fin 2)⟩ : DualSquarePositiveEdge)).toEdge : Sym2 SquareVertex) := by
    intro heq
    apply hnot
    rw [mem_walkEdgeFinset_iff]
    simpa [heq] using he
  induction e using Sym2.ind with
  | _ u v =>
      have huv : squareGraph.Adj u v := c.adj_of_mem_edges he
      rcases (cubicGraph_adj_iff_exists_stepFrom u v).mp huv with ⟨i, rfl⟩
      rcases i with ⟨i, b⟩
      fin_cases i <;> cases b <;>
        simp [squareEdgeCrossesFaceVerticalRayBool,
          squareEdgeCrossesFaceVerticalRay,
          dualToPrimalCrossingPositiveEdge, SquarePositiveEdge.toEdge,
          squarePerp, cubicStepFrom, cubicDirectionIncrement] at hne ⊢ <;>
        try omega
      all_goals
        intro hx
        by_cases hu : u 1 = f 1 + 1
        · exfalso
          simp [funext_iff, hu, hx] at hne
          try omega
        · omega

/-- The edge-level crossing equivalence sends a positive dual bond back to its canonical crossed
positive primal bond. -/
theorem squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge
    (d : DualSquarePositiveEdge) :
    squareEdgeDualCrossingEquiv.symm d.toEdge =
      (dualToPrimalCrossingPositiveEdge d).toEdge := by
  have hdual :
      squarePositiveEdgeDualCrossingEmbedding
          (dualToPrimalCrossingPositiveEdge d) = d.toEdge := by
    unfold squarePositiveEdgeDualCrossingEmbedding squareEdgeDualCrossingEquiv
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.trans_apply]
    rw [SquarePositiveEdge.edgeEquiv_symm_squarePositiveEdgeEmbedding]
    change (primalToDualCrossingPositiveEdge
      (dualToPrimalCrossingPositiveEdge d)).toEdge = d.toEdge
    rw [primalToDual_dualToPrimalCrossingPositiveEdge]
  rw [← hdual,
    squareEdgeDualCrossingEquiv_symm_squarePositiveEdgeDualCrossingEmbedding]

/-- The mod-two face index of a closed primal walk is unchanged across a positive dual step whose
crossed primal bond does not occur in the walk. -/
theorem closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o)
    (d : DualSquarePositiveEdge)
    (hnot : (dualToPrimalCrossingPositiveEdge d).toEdge ∉ walkEdgeFinset c) :
    closedSquareWalkFaceParity c d.base =
      closedSquareWalkFaceParity c
        (cubicStepFrom d.base (d.axis, true)) := by
  rcases d with ⟨f, axis⟩
  fin_cases axis
  · change (dualToPrimalCrossingPositiveEdge
        (⟨f, (0 : Fin 2)⟩ : DualSquarePositiveEdge)).toEdge ∉
      walkEdgeFinset c at hnot
    change closedSquareWalkFaceParity c f =
      closedSquareWalkFaceParity c (cubicStepFrom f ((0 : Fin 2), true))
    unfold closedSquareWalkFaceParity
    rw [closedWalk_horizontalRayCount_stepRight_eq_of_crossed_not_mem c f hnot]
  · change (dualToPrimalCrossingPositiveEdge
        (⟨f, (1 : Fin 2)⟩ : DualSquarePositiveEdge)).toEdge ∉
      walkEdgeFinset c at hnot
    change closedSquareWalkFaceParity c f =
      closedSquareWalkFaceParity c (cubicStepFrom f ((1 : Fin 2), true))
    unfold closedSquareWalkFaceParity
    rw [closedWalk_faceRayCount_mod_two_eq c f,
      closedWalk_faceRayCount_mod_two_eq c
        (cubicStepFrom f ((1 : Fin 2), true)),
      closedWalk_verticalRayCount_stepUp_eq_of_crossed_not_mem c f hnot]

/-- Adjacent shifted-dual faces have the same closed-walk face parity unless their dual bond
crosses a primal bond of the closed walk. -/
theorem closedSquareWalkFaceParity_eq_of_dualAdj_of_crossed_not_mem
    {o : SquareVertex} (c : squareGraph.Walk o o)
    {u v : DualSquareVertex} (huv : dualSquareGraph.Adj u v)
    (hnot : squareEdgeDualCrossingEquiv.symm
      (⟨s(u, v), dualSquareGraph.mem_edgeSet.mpr huv⟩ : DualSquareEdge) ∉
        walkEdgeFinset c) :
    closedSquareWalkFaceParity c u = closedSquareWalkFaceParity c v := by
  let ed : DualSquareEdge :=
    ⟨s(u, v), dualSquareGraph.mem_edgeSet.mpr huv⟩
  let d : DualSquarePositiveEdge := SquarePositiveEdge.edgeEquiv.symm ed
  have hdEdge : d.toEdge = ed := by
    change SquarePositiveEdge.edgeEquiv d = ed
    simp [d]
  have hnotd : (dualToPrimalCrossingPositiveEdge d).toEdge ∉
      walkEdgeFinset c := by
    rw [← squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge d,
      hdEdge]
    exact hnot
  have hparity :=
    closedSquareWalkFaceParity_eq_of_positiveDualStep_of_crossed_not_mem c d hnotd
  have hendpoints :
      s(d.base, cubicStepFrom d.base (d.axis, true)) = s(u, v) := by
    exact congrArg Subtype.val hdEdge
  rw [Sym2.eq_iff] at hendpoints
  rcases hendpoints with hsame | hswap
  · rcases hsame with ⟨hdu, hdv⟩
    calc
      closedSquareWalkFaceParity c u =
          closedSquareWalkFaceParity c d.base := congrArg _ hdu.symm
      _ = closedSquareWalkFaceParity c
          (cubicStepFrom d.base (d.axis, true)) := hparity
      _ = closedSquareWalkFaceParity c v := congrArg _ hdv
  · rcases hswap with ⟨hdv, hdu⟩
    calc
      closedSquareWalkFaceParity c u = closedSquareWalkFaceParity c
          (cubicStepFrom d.base (d.axis, true)) := congrArg _ hdu.symm
      _ = closedSquareWalkFaceParity c d.base := hparity.symm
      _ = closedSquareWalkFaceParity c v := congrArg _ hdv

/-- Face parity is constant along a dual walk when no crossed primal bond of that walk occurs in
the closed primal walk. -/
theorem closedSquareWalkFaceParity_eq_along_dualWalk_of_crossed_not_mem
    {o u v : SquareVertex} (c : squareGraph.Walk o o)
    (q : dualSquareGraph.Walk u v)
    (hnot : ∀ ed : DualSquareEdge, ed ∈ walkEdgeFinset q →
      squareEdgeDualCrossingEquiv.symm ed ∉ walkEdgeFinset c) :
    closedSquareWalkFaceParity c u = closedSquareWalkFaceParity c v := by
  induction q with
  | nil => rfl
  | @cons u v z huv q ih =>
      let ed : DualSquareEdge :=
        ⟨s(u, v), dualSquareGraph.mem_edgeSet.mpr huv⟩
      have hed : ed ∈ walkEdgeFinset (SimpleGraph.Walk.cons huv q) := by
        rw [mem_walkEdgeFinset_iff]
        simp [ed]
      have hstep := closedSquareWalkFaceParity_eq_of_dualAdj_of_crossed_not_mem
        c huv (hnot ed hed)
      have htail : ∀ ed : DualSquareEdge, ed ∈ walkEdgeFinset q →
          squareEdgeDualCrossingEquiv.symm ed ∉ walkEdgeFinset c := by
        intro f hf
        apply hnot f
        rw [mem_walkEdgeFinset_iff] at hf ⊢
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr hf
      exact hstep.trans (ih htail)

/-- If the face parity differs at the endpoints of a dual walk, one dual bond of that walk crosses
a primal bond of the closed walk. -/
theorem exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne
    {o u v : SquareVertex} (c : squareGraph.Walk o o)
    (q : dualSquareGraph.Walk u v)
    (hne : closedSquareWalkFaceParity c u ≠
      closedSquareWalkFaceParity c v) :
    ∃ ed ∈ walkEdgeFinset q,
      squareEdgeDualCrossingEquiv.symm ed ∈ walkEdgeFinset c := by
  by_contra hcross
  push Not at hcross
  exact hne
    (closedSquareWalkFaceParity_eq_along_dualWalk_of_crossed_not_mem c q hcross)

/-! ### A boundary-free exterior closure for a bottom-to-top walk -/

/-- Direction word from `(b,n)` to `(a,-n)` which first follows the top boundary to the
exterior column `x = -1`, descends that column, and then follows the bottom boundary. -/
def brLeftExteriorClosureSteps (n a b : ℕ) : List (CubicDirection 2) :=
  List.replicate (b + 1) (⟨0, by decide⟩, false) ++
    (List.replicate (2 * n) (⟨1, by decide⟩, false) ++
      List.replicate (a + 1) (⟨0, by decide⟩, true))

theorem cubicEndpointFrom_brLeftExteriorClosureSteps (n a b : ℕ) :
    cubicEndpointFrom (squareVertex (b : ℤ) (n : ℤ))
      (brLeftExteriorClosureSteps n a b) =
        squareVertex (a : ℤ) (-(n : ℤ)) := by
  simp only [brLeftExteriorClosureSteps, cubicEndpointFrom_append,
    cubicEndpointFrom_replicate_pos, cubicEndpointFrom_replicate_neg]
  ext i
  fin_cases i
  · simp [squareVertex, Function.update]
  · simp [squareVertex, Function.update]
    omega

/-- The left exterior closure walk used to turn a bottom-to-top primal walk into a closed walk. -/
def brLeftExteriorClosureWalk (n a b : ℕ) :
    squareGraph.Walk (squareVertex (b : ℤ) (n : ℤ))
      (squareVertex (a : ℤ) (-(n : ℤ))) :=
  (cubicWalkFrom (squareVertex (b : ℤ) (n : ℤ))
    (brLeftExteriorClosureSteps n a b)).copy rfl
      (cubicEndpointFrom_brLeftExteriorClosureSteps n a b)

/-- Every vertex of the exterior closure lies either on the exterior column or on one of the
two horizontal sides of the square. -/
theorem mem_brLeftExteriorClosureWalk_support
    {n a b : ℕ} {z : SquareVertex}
    (hz : z ∈ (brLeftExteriorClosureWalk n a b).support) :
    z 0 = -1 ∨ z 1 = (n : ℤ) ∨ z 1 = -(n : ℤ) := by
  simp only [brLeftExteriorClosureWalk, SimpleGraph.Walk.support_copy] at hz
  let x₀ := squareVertex (b : ℤ) (n : ℤ)
  let x₁ := squareVertex (-1) (n : ℤ)
  let x₂ := squareVertex (-1) (-(n : ℤ))
  let s₀ : List (CubicDirection 2) :=
    List.replicate (b + 1) (⟨0, by decide⟩, false)
  let s₁ : List (CubicDirection 2) :=
    List.replicate (2 * n) (⟨1, by decide⟩, false)
  let s₂ : List (CubicDirection 2) :=
    List.replicate (a + 1) (⟨0, by decide⟩, true)
  have he₀ : cubicEndpointFrom x₀ s₀ = x₁ := by
    ext i
    fin_cases i <;>
      simp [x₀, x₁, s₀, squareVertex,
        cubicEndpointFrom_replicate_neg, Function.update]
  have he₁ : cubicEndpointFrom x₁ s₁ = x₂ := by
    ext i
    fin_cases i
    · simp [x₁, x₂, s₁, squareVertex,
        cubicEndpointFrom_replicate_neg, Function.update]
    · simp [x₁, x₂, s₁, squareVertex,
        cubicEndpointFrom_replicate_neg, Function.update]
      omega
  have hz' : z ∈ cubicVerticesFrom x₀ (s₀ ++ (s₁ ++ s₂)) := by
    simpa [x₀, s₀, s₁, s₂, brLeftExteriorClosureSteps] using hz
  rw [mem_cubicVerticesFrom_append_iff] at hz'
  rcases hz' with hz₀ | hz'
  · have hy := cubicVerticesFrom_replicate_neg_coord_eq_of_ne
      x₀ (0 : Fin 2) (1 : Fin 2) (b + 1) (by decide) hz₀
    exact Or.inr (Or.inl (by simpa [x₀, squareVertex] using hy))
  · rw [he₀, mem_cubicVerticesFrom_append_iff] at hz'
    rcases hz' with hz₁ | hz₂
    · have hx := cubicVerticesFrom_replicate_neg_coord_eq_of_ne
        x₁ (1 : Fin 2) (0 : Fin 2) (2 * n) (by decide) hz₁
      exact Or.inl (by simpa [x₁, squareVertex] using hx)
    · rw [he₁] at hz₂
      have hy := cubicVerticesFrom_replicate_pos_coord_eq_of_ne
        x₂ (0 : Fin 2) (1 : Fin 2) (a + 1) (by decide) hz₂
      exact Or.inr (Or.inr (by simpa [x₂, squareVertex] using hy))

/-- Rays based weakly to the right of the exterior column do not cross the exterior closure. -/
theorem brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    {n a b : ℕ} (f : DualSquareVertex) (hf : -1 ≤ f 0) :
    (brLeftExteriorClosureWalk n a b).edges.countP
      (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  simp only [brLeftExteriorClosureWalk, SimpleGraph.Walk.edges_copy,
    brLeftExteriorClosureSteps]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  rw [cubicWalkFrom_edges_append, List.countP_append]
  have hfirst := horizontalRayCount_cubicWalkFrom_replicate_horizontal
    (squareVertex (b : ℤ) (n : ℤ)) f (b + 1) false
  have hmiddle := horizontalRayCount_cubicWalkFrom_replicate_vertical_neg
    (cubicEndpointFrom (squareVertex (b : ℤ) (n : ℤ))
      (List.replicate (b + 1) (⟨0, by decide⟩, false))) f (2 * n)
  have hlast := horizontalRayCount_cubicWalkFrom_replicate_horizontal
    (cubicEndpointFrom
      (cubicEndpointFrom (squareVertex (b : ℤ) (n : ℤ))
        (List.replicate (b + 1) (⟨0, by decide⟩, false)))
      (List.replicate (2 * n) (⟨1, by decide⟩, false))) f (a + 1) true
  rw [hfirst, hmiddle, hlast]
  simp [squareVertex, cubicEndpointFrom_replicate_neg, Function.update]
  omega

/-- No bond of the exterior closure belongs to the boundary-free square support. -/
theorem walkEdgeFinset_brLeftExteriorClosureWalk_disjoint_boundaryFree
    (n a b : ℕ) :
    Disjoint (walkEdgeFinset (brLeftExteriorClosureWalk n a b))
      (squareBoundaryFreeRectangleEdges (2 * n) n) := by
  classical
  rw [Finset.disjoint_left]
  intro e heClosure heAllowed
  have heRaw : (e : Sym2 SquareVertex) ∈
      (brLeftExteriorClosureWalk n a b).edges :=
    (mem_walkEdgeFinset_iff (brLeftExteriorClosureWalk n a b) e).mp heClosure
  have hfst := mem_brLeftExteriorClosureWalk_support
    ((brLeftExteriorClosureWalk n a b).mem_support_of_mem_edges heRaw
      (Sym2.out_fst_mem e.1))
  have hsnd := mem_brLeftExteriorClosureWalk_support
    ((brLeftExteriorClosureWalk n a b).mem_support_of_mem_edges heRaw
      (Sym2.out_snd_mem e.1))
  rw [squareBoundaryFreeRectangleEdges, Finset.mem_filter] at heAllowed
  have hfstRect := endpoint_mem_squareRectangle_of_edge_mem
    heAllowed.1 (Sym2.out_fst_mem e.1)
  have hsndRect := endpoint_mem_squareRectangle_of_edge_mem
    heAllowed.1 (Sym2.out_snd_mem e.1)
  have hfstCoords := mem_squareRectangleVertices_iff.mp hfstRect
  have hsndCoords := mem_squareRectangleVertices_iff.mp hsndRect
  apply heAllowed.2
  constructor
  · rcases hfst with hleft | htop | hbottom
    · omega
    · exact Or.inr (Or.inr (Or.inr htop))
    · exact Or.inr (Or.inr (Or.inl hbottom))
  · rcases hsnd with hleft | htop | hbottom
    · omega
    · exact Or.inr (Or.inr (Or.inr htop))
    · exact Or.inr (Or.inr (Or.inl hbottom))

/-- A walk whose bonds lie in the boundary-free rectangle stays in the rectangle, provided its
terminal vertex does. -/
theorem walk_support_mem_squareRectangle_of_boundaryFree_edges
    {m n : ℕ} {u v : SquareVertex} (w : squareGraph.Walk u v)
    (hv : v ∈ squareRectangleVertices m n)
    (hw : walkEdgeFinset w ⊆ squareBoundaryFreeRectangleEdges m n) :
    ∀ z ∈ w.support, z ∈ squareRectangleVertices m n := by
  classical
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hv
  · let ee : SquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
    have heAllowed : ee ∈ squareBoundaryFreeRectangleEdges m n :=
      hw ((mem_walkEdgeFinset_iff w ee).mpr he)
    exact endpoint_mem_squareRectangle_of_edge_mem
      (Finset.mem_filter.mp heAllowed).1 hze

private theorem verticalRayCount_eq_zero_of_support_right_of_face
    {u v : SquareVertex} (p : squareGraph.Walk u v) (f : DualSquareVertex)
    (hright : ∀ z ∈ p.support, f 0 < z 0) :
    p.edges.countP (squareEdgeCrossesFaceVerticalRayBool f) = 0 := by
  classical
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hright x (p.fst_mem_support_of_mem_edges he)
      have hy := hright y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceVerticalRayBool,
        squareEdgeCrossesFaceVerticalRay]
      omega

/-- A square walk from the bottom side to the top side has odd horizontal-ray count when the
ray starts in the left exterior face column. -/
theorem odd_horizontalRayCount_of_bottom_top_walk
    {n a b : ℕ}
    (p : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    (f : DualSquareVertex) (hf₀ : f 0 = -1)
    (hf₁ : -(n : ℤ) ≤ f 1) (hf₁' : f 1 < (n : ℤ)) :
    Odd (p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f)) := by
  have hright : ∀ z ∈ p.support, f 0 < z 0 := by
    intro z hz
    have hzBox := hbox z hz
    omega
  have hcutOdd : Odd (p.edges.countP
      (SimpleGraph.Walk.edgeCrossesSetBool (squareFaceNorthEast f))) := by
    apply (SimpleGraph.Walk.odd_countP_edges_edgeCrossesSet_iff
      (squareFaceNorthEast f) p).mpr
    refine Or.inr ⟨?_, ?_⟩
    · have hend := hbox _ p.end_mem_support
      simp [squareFaceNorthEast, squareVertex]
      omega
    · intro hstart
      simp [squareFaceNorthEast, squareVertex] at hstart
      omega
  have hsum := walk_northEastCut_count_eq_add_faceRays p f
  have hvertical := verticalRayCount_eq_zero_of_support_right_of_face p f hright
  rw [hsum, hvertical, add_zero] at hcutOdd
  exact hcutOdd

private theorem horizontalRayCount_eq_zero_of_support_left_of_face
    {u v : SquareVertex} (p : squareGraph.Walk u v) (f : DualSquareVertex)
    (hleft : ∀ z ∈ p.support, z 0 ≤ f 0) :
    p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool f) = 0 := by
  classical
  rw [List.countP_eq_zero]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      have hx := hleft x (p.fst_mem_support_of_mem_edges he)
      have hy := hleft y (p.snd_mem_support_of_mem_edges he)
      simp [squareEdgeCrossesFaceHorizontalRayBool,
        squareEdgeCrossesFaceHorizontalRay]
      omega

/-- Closing a bottom-to-top square walk along the left exterior boundary gives different
mod-two face indices on the left source and right target columns. -/
theorem brClosedBottomTopWalk_faceParity_ne
    {n a b : ℕ}
    (p : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)))
    (hbox : ∀ z ∈ p.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ))
    {x y : DualSquareVertex}
    (hx₀ : x 0 = -1) (hx₁ : -(n : ℤ) ≤ x 1) (hx₁' : x 1 < (n : ℤ))
    (hy₀ : y 0 = 2 * (n : ℤ)) :
    closedSquareWalkFaceParity
        (p.append (brLeftExteriorClosureWalk n a b)) x ≠
      closedSquareWalkFaceParity
        (p.append (brLeftExteriorClosureWalk n a b)) y := by
  let c := p.append (brLeftExteriorClosureWalk n a b)
  have hxOdd := odd_horizontalRayCount_of_bottom_top_walk p hbox x hx₀ hx₁ hx₁'
  have hxClosure := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) x (by omega)
  have hyPrimal : p.edges.countP (squareEdgeCrossesFaceHorizontalRayBool y) = 0 :=
    horizontalRayCount_eq_zero_of_support_left_of_face p y (by
      intro z hz
      have hzBox := hbox z hz
      omega)
  have hyClosure := brLeftExteriorClosureWalk_horizontalRayCount_eq_zero
    (n := n) (a := a) (b := b) y (by omega)
  have hxParity : closedSquareWalkFaceParity c x = 1 := by
    unfold closedSquareWalkFaceParity
    simp only [c, SimpleGraph.Walk.edges_append, List.countP_append, hxClosure, add_zero]
    exact Nat.odd_iff.mp hxOdd
  have hyParity : closedSquareWalkFaceParity c y = 0 := by
    unfold closedSquareWalkFaceParity
    simp [c, SimpleGraph.Walk.edges_append, List.countP_append, hyPrimal, hyClosure]
  rw [hxParity, hyParity]
  norm_num

/-- A dual positive bond whose endpoints lie in the exploration frame cannot cross the
artificial exterior closure. -/
theorem dualToPrimalCrossingPositiveEdge_not_mem_brLeftExteriorClosureWalk
    {n a b : ℕ} (d : DualSquarePositiveEdge)
    (hbase : d.base ∈ brLeftmostDualFaces n)
    (hstep : cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n) :
    (dualToPrimalCrossingPositiveEdge d).toEdge ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n a b) := by
  intro hmem
  have hraw : ((dualToPrimalCrossingPositiveEdge d).toEdge : Sym2 SquareVertex) ∈
      (brLeftExteriorClosureWalk n a b).edges :=
    (mem_walkEdgeFinset_iff (brLeftExteriorClosureWalk n a b) _).mp hmem
  let pe := dualToPrimalCrossingPositiveEdge d
  have hraw' : s(pe.base, cubicStepFrom pe.base (pe.axis, true)) ∈
      (brLeftExteriorClosureWalk n a b).edges := by
    simpa [pe, SquarePositiveEdge.toEdge] using hraw
  have hpbase := mem_brLeftExteriorClosureWalk_support
    ((brLeftExteriorClosureWalk n a b).fst_mem_support_of_mem_edges hraw')
  have hpstep := mem_brLeftExteriorClosureWalk_support
    ((brLeftExteriorClosureWalk n a b).snd_mem_support_of_mem_edges hraw')
  have hbaseCoords := mem_brLeftmostDualFaces_iff.mp hbase
  have hstepCoords := mem_brLeftmostDualFaces_iff.mp hstep
  rcases d with ⟨f, axis⟩
  fin_cases axis
  · simp [pe, dualToPrimalCrossingPositiveEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hpbase hpstep hbaseCoords hstepCoords
    rcases hpbase with hpbase | hpbase | hpbase <;>
      rcases hpstep with hpstep | hpstep | hpstep <;> omega
  · simp [pe, dualToPrimalCrossingPositiveEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hpbase hpstep hbaseCoords hstepCoords
    rcases hpbase with hpbase | hpbase | hpbase <;>
      rcases hpstep with hpstep | hpstep | hpstep <;> omega

/-- Unoriented form of the preceding frame-versus-closure separation lemma. -/
theorem squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk
    {n a b : ℕ} (ed : DualSquareEdge)
    (hendpoints : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n) :
    squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n a b) := by
  let d : DualSquarePositiveEdge := SquarePositiveEdge.edgeEquiv.symm ed
  have hdEdge : d.toEdge = ed := by
    change SquarePositiveEdge.edgeEquiv d = ed
    simp [d]
  have hbase : d.base ∈ brLeftmostDualFaces n := by
    apply hendpoints d.base
    rw [← hdEdge]
    simp [SquarePositiveEdge.toEdge, Sym2.mem_iff]
  have hstep : cubicStepFrom d.base (d.axis, true) ∈ brLeftmostDualFaces n := by
    apply hendpoints (cubicStepFrom d.base (d.axis, true))
    rw [← hdEdge]
    simp [SquarePositiveEdge.toEdge, Sym2.mem_iff]
  rw [← hdEdge, squareEdgeDualCrossingEquiv_symm_dualPositiveEdge_toEdge]
  exact dualToPrimalCrossingPositiveEdge_not_mem_brLeftExteriorClosureWalk
    d hbase hstep

/-- A boundary-free bottom-to-top primal crossing prevents the stopped closed-dual exploration
from reaching the right target column. -/
theorem brSquareVerticalCrossingEvent_subset_brRightTargetsUnreachedEvent (n : ℕ) :
    brSquareVerticalCrossingEvent n ⊆ brRightTargetsUnreachedEvent n := by
  classical
  intro ω hvertical
  by_contra hunreached
  have hreached : ω ∈ brRightTargetsReachedEvent n := by
    rw [brRightTargetsReachedEvent_eq_compl_unreached, Set.mem_compl_iff]
    exact hunreached
  obtain ⟨yDual, hyTarget, xDual, hxSource, wDual, hwDualOpen⟩ :=
    mem_brRightTargetsReachedEvent_iff_exists_open_walk.mp hreached
  simp only [brSquareVerticalCrossingEvent, Set.mem_iUnion] at hvertical
  obtain ⟨xPrimal, hxBottom, yPrimal, hyTop, p, hpOpen, hpAllowed⟩ := hvertical
  have hxData := mem_brSquareBottomSide_iff.mp hxBottom
  have hyData := mem_brSquareTopSide_iff.mp hyTop
  let a := (xPrimal 0).toNat
  let b := (yPrimal 0).toNat
  have haCast : (a : ℤ) = xPrimal 0 := by
    simp [a, Int.toNat_of_nonneg hxData.1]
  have hbCast : (b : ℤ) = yPrimal 0 := by
    simp [b, Int.toNat_of_nonneg hyData.1]
  have hxEq : xPrimal = squareVertex (a : ℤ) (-(n : ℤ)) := by
    ext i
    fin_cases i
    · simpa [squareVertex] using haCast.symm
    · simpa [squareVertex] using hxData.2.2
  have hyEq : yPrimal = squareVertex (b : ℤ) (n : ℤ) := by
    ext i
    fin_cases i
    · simpa [squareVertex] using hbCast.symm
    · simpa [squareVertex] using hyData.2.2
  let p' : squareGraph.Walk (squareVertex (a : ℤ) (-(n : ℤ)))
      (squareVertex (b : ℤ) (n : ℤ)) := p.copy hxEq hyEq
  have hyRect : yPrimal ∈ squareRectangleVertices (2 * n) n :=
    mem_squareRectangleVertices_iff.mpr
      ⟨hyData.1, hyData.2.1, by omega, by omega⟩
  have hpRect := walk_support_mem_squareRectangle_of_boundaryFree_edges
    p hyRect hpAllowed
  have hpBox : ∀ z ∈ p'.support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) ∧
        -(n : ℤ) ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
    intro z hz
    apply mem_squareRectangleVertices_iff.mp
    apply hpRect z
    simpa [p'] using hz
  let q := wDual.map (brLeftmostDualToAmbientHom n)
  have hqSupport : ∀ z ∈ q.support, z ∈ brLeftmostDualFaces n := by
    intro z hz
    simp only [q, SimpleGraph.Walk.support_map, List.mem_map] at hz
    rcases hz with ⟨zFrame, _hzFrame, rfl⟩
    exact zFrame.2
  have hxFrame := mem_brLeftmostDualFaces_iff.mp xDual.2
  have hx₀ : xDual.1 0 = -1 := mem_brLeftmostDualSources_iff.mp hxSource
  have hy₀ : yDual.1 0 = 2 * (n : ℤ) :=
    mem_brRightmostDualTargets_iff.mp hyTarget
  let c := p'.append (brLeftExteriorClosureWalk n a b)
  have hparity : closedSquareWalkFaceParity c xDual.1 ≠
      closedSquareWalkFaceParity c yDual.1 := by
    exact brClosedBottomTopWalk_faceParity_ne p' hpBox hx₀ hxFrame.2.2.1
      hxFrame.2.2.2 hy₀
  obtain ⟨ed, hedq, hedc⟩ :=
    exists_dualWalk_edge_crossing_closedWalk_of_faceParity_ne c q hparity
  have hedRaw : (ed : Sym2 DualSquareVertex) ∈ q.edges :=
    (mem_walkEdgeFinset_iff q ed).mp hedq
  have hedEndpoints : ∀ z ∈ (ed : Sym2 DualSquareVertex),
      z ∈ brLeftmostDualFaces n := by
    intro z hz
    apply hqSupport z
    exact q.mem_support_of_mem_edges hedRaw hz
  have hedNotClosure : squareEdgeDualCrossingEquiv.symm ed ∉
      walkEdgeFinset (brLeftExteriorClosureWalk n a b) :=
    squareEdgeDualCrossingEquiv_symm_not_mem_brLeftExteriorClosureWalk
      ed hedEndpoints
  have hedPrimal : squareEdgeDualCrossingEquiv.symm ed ∈ walkEdgeFinset p' := by
    have hedc' : squareEdgeDualCrossingEquiv.symm ed ∈
        walkEdgeFinset (p'.append (brLeftExteriorClosureWalk n a b)) := by
      simpa only [c] using hedc
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at hedc'
    rcases hedc' with hp | hclosure
    · exact (mem_walkEdgeFinset_iff p' _).mpr hp
    · exact (hedNotClosure ((mem_walkEdgeFinset_iff _ _).mpr hclosure)).elim
  have hpAllowed' : walkEdgeFinset p' ⊆
      squareBoundaryFreeRectangleEdges (2 * n) n := by
    intro e he
    apply hpAllowed
    rw [mem_walkEdgeFinset_iff] at he ⊢
    simpa [p', SimpleGraph.Walk.edges_copy] using he
  have hpOpen' : walkIsOpen ω p' := by
    simpa [p'] using (walkIsOpen_copy p hxEq hyEq).mpr hpOpen
  have hedAllowed : squareEdgeDualCrossingEquiv.symm ed ∈
      squareBoundaryFreeRectangleEdges (2 * n) n := hpAllowed' hedPrimal
  have hedOpen : squareEdgeDualCrossingEquiv.symm ed ∈ ω := by
    have hraw := (mem_walkEdgeFinset_iff p' _).mp hedPrimal
    have hopen := hpOpen' _ hraw
    simpa only [Subtype.ext_iff] using hopen
  have hedRawMap := hedRaw
  simp only [q, SimpleGraph.Walk.edges_map] at hedRawMap
  rw [List.mem_map] at hedRawMap
  rcases hedRawMap with ⟨eFrame, heFrame, hmap⟩
  have heFrameGraph : eFrame ∈ (brLeftmostDualGraph n).edgeSet :=
    wDual.edges_subset_edgeSet heFrame
  let eFrame' : (brLeftmostDualGraph n).edgeSet := ⟨eFrame, heFrameGraph⟩
  have heEmbedded : brLeftmostDualEdgeEmbedding n eFrame' = ed := by
    apply Subtype.ext
    exact hmap
  have heExplorationOpen : eFrame ∈
      brClosedDualExplorationConfiguration n ω := hwDualOpen eFrame heFrame
  have hopenAlternative :=
    (mem_brClosedDualExplorationConfiguration_iff_of_mem_edgeSet heFrameGraph).mp
      heExplorationOpen
  rw [show brLeftmostDualEdgeEmbedding n ⟨eFrame, heFrameGraph⟩ = ed by
    simpa [eFrame'] using heEmbedded] at hopenAlternative
  exact hopenAlternative.elim (· hedAllowed) (· hedOpen)

end

end Percolation
