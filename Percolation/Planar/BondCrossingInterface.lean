import Percolation.Planar.SiteCrossingInterface

/-!
# The bond-crossing interface in a finite square rectangle

The finite site interface can be applied to the set of vertices which are bond-reachable from
the left side of a rectangle.  On failure of an open bond crossing, every primal edge crossed by
the resulting shifted-dual interface is closed.  Consequently the bottom--top interface walk is
open in the induced dual configuration.

This is the deterministic planar crossing alternative used in Grimmett's self-duality argument.
It is proved entirely inside the finite rectangle and does not appeal to an external Jordan-curve
theorem.
-/

namespace Percolation

open scoped Sym2

/-- Vertices connected by open rectangle bonds to some vertex on the left side. -/
def bondRectangleLeftReachableSet
    (m n : ℕ) (ω : EdgeConfiguration 2) : Set SquareVertex :=
  {y | ∃ x : SquareVertex, x ∈ squareRectangleLeft m n ∧
    ω ∈ connectionEventIn 2 (squareRectangleEdges m n) x y}

theorem mem_bondRectangleLeftReachableSet_iff
    {m n : ℕ} {ω : EdgeConfiguration 2} {y : SquareVertex} :
    y ∈ bondRectangleLeftReachableSet m n ω ↔
      ∃ x : SquareVertex, x ∈ squareRectangleLeft m n ∧
        ω ∈ connectionEventIn 2 (squareRectangleEdges m n) x y :=
  Iff.rfl

/-- Every left-side vertex is bond-reachable, using the nil walk. -/
theorem mem_bondRectangleLeftReachableSet_of_mem_left
    {m n : ℕ} {ω : EdgeConfiguration 2} {x : SquareVertex}
    (hx : x ∈ squareRectangleLeft m n) :
    x ∈ bondRectangleLeftReachableSet m n ω := by
  refine ⟨x, hx, SimpleGraph.Walk.nil, ?_, ?_⟩
  · intro e he
    simp at he
  · intro e he
    simp at he

/-- Bond reachability is closed under an open adjacent step which stays in the rectangle. -/
theorem bondRectangleLeftReachableSet_step
    {m n : ℕ} {ω : EdgeConfiguration 2} {u v : SquareVertex}
    (hu : u ∈ bondRectangleLeftReachableSet m n ω)
    (huRect : u ∈ squareRectangleVertices m n)
    (hvRect : v ∈ squareRectangleVertices m n)
    (huv : squareGraph.Adj u v)
    (hopen : (⟨s(u, v), (SimpleGraph.mem_edgeSet squareGraph).mpr huv⟩ : SquareEdge) ∈ ω) :
    v ∈ bondRectangleLeftReachableSet m n ω := by
  rcases hu with ⟨x, hxLeft, w, hwOpen, hwEdges⟩
  let step : squareGraph.Walk u v := SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
  have hstepOpen : walkIsOpen ω step := by
    intro e he
    have heq : e = s(u, v) := by
      simpa [step, SimpleGraph.Walk.edges_cons] using he
    subst e
    simpa using hopen
  have hstepRect : ∀ z ∈ step.support, z ∈ squareRectangleVertices m n := by
    intro z hz
    simp only [step, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons] at hz
    rcases hz with rfl | (rfl | hz)
    · exact huRect
    · exact hvRect
    · simp at hz
  have hstepEdges : walkEdgeFinset step ⊆ squareRectangleEdges m n :=
    walkEdgeFinset_subset_squareRectangleEdges_of_support step hstepRect
  refine ⟨x, hxLeft, w.append step, walkIsOpen_append hwOpen hstepOpen, ?_⟩
  intro e he
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append, List.mem_append] at he
  rcases he with he | he
  · exact hwEdges ((mem_walkEdgeFinset_iff w e).mpr he)
  · exact hstepEdges ((mem_walkEdgeFinset_iff step e).mpr he)

/-- If the bond crossing fails, the bond-reachable set has no open-site crossing. -/
theorem bondRectangleLeftReachableSet_not_mem_siteCrossing_of_not_bondCrossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n) :
    bondRectangleLeftReachableSet m n ω ∉ siteSquareRectangleCrossingEvent m n := by
  intro hsite
  simp only [siteSquareRectangleCrossingEvent, Set.mem_iUnion] at hsite
  rcases hsite with ⟨x, hxLeft, y, hyRight, w, _hwRect, hwReachable⟩
  have hyReachable : y ∈ bondRectangleLeftReachableSet m n ω :=
    hwReachable y w.end_mem_support
  rcases hyReachable with ⟨u, huLeft, huy⟩
  apply hno
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion]
  exact ⟨u, huLeft, y, hyRight, huy⟩

private theorem interfaceReachableEndpoint_mem_rectangle_of_bond_not_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n
      (bondRectangleLeftReachableSet m n ω)) :
    siteRectangleInterfaceReachableEndpoint m n
        (bondRectangleLeftReachableSet m n ω) b ∈
      squareRectangleVertices m n := by
  let eta := bondRectangleLeftReachableSet m n ω
  let r := siteRectangleInterfaceReachableEndpoint m n eta b
  let u := siteRectangleInterfaceUnreachableEndpoint m n eta b
  have hnoSite : eta ∉ siteSquareRectangleCrossingEvent m n :=
    bondRectangleLeftReachableSet_not_mem_siteCrossing_of_not_bondCrossing hno
  have huBoundary :=
    interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hnoSite hb
  have huRect : u ∈ squareRectangleVertices m n :=
    (mem_siteRectangleLeftReachableBoundary_iff m n eta u).mp huBoundary |>.1
  have hrFrame := interfaceReachableEndpoint_mem_frame hb
  change -1 ≤ r 0 ∧ r 0 ≤ (m : ℤ) + 1 ∧
    -(n : ℤ) ≤ r 1 ∧ r 1 ≤ (n : ℤ) at hrFrame
  have hrNotRight : r 0 ≠ (m : ℤ) + 1 :=
    interfaceReachableEndpoint_ne_rightColumn_of_not_crossing hnoSite hb
  have hrNotLeft : r 0 ≠ -1 := by
    intro hrLeft
    have hruAdj : squareGraph.Adj r u := interfaceEndpoint_adj m n eta b
    have hdist : cubicL1Dist r u = 1 := by
      rcases (cubicGraph_adj_iff_exists_stepFrom r u).mp hruAdj with ⟨a, ha⟩
      rw [ha]
      exact cubicL1Dist_stepFrom r a
    have hcoord : (u 0 - r 0).natAbs ≤ 1 :=
      (cubicL1Dist_coord_le r u (0 : Fin 2)).trans_eq hdist
    have hnonneg : 0 ≤ u 0 - r 0 := by
      have huBounds := mem_squareRectangleVertices_iff.mp huRect
      omega
    have hcoordInt : ((u 0 - r 0).natAbs : ℤ) ≤ (1 : ℤ) := by
      exact_mod_cast hcoord
    rw [Int.natAbs_of_nonneg hnonneg] at hcoordInt
    have hcoordInt' : u 0 + 1 ≤ (1 : ℤ) := by
      simpa [hrLeft] using hcoordInt
    have huZero : u 0 = 0 := by
      have huBounds := mem_squareRectangleVertices_iff.mp huRect
      omega
    have huLeft : u ∈ squareRectangleLeft m n := by
      rw [mem_squareRectangleLeft_iff]
      have huBounds := mem_squareRectangleVertices_iff.mp huRect
      exact ⟨huZero, huBounds.2.2.1, huBounds.2.2.2⟩
    have huEta : u ∈ eta :=
      mem_bondRectangleLeftReachableSet_of_mem_left huLeft
    have huOrdinary : u ∈ siteRectangleLeftReachableVertices m n eta :=
      mem_siteRectangleLeftReachableVertices_of_mem_left huLeft huEta
    have huFramed : siteRectangleFramedReachable m n eta u :=
      (siteRectangleFramedReachable_iff_reachable_of_mem_rectangle huRect).mpr huOrdinary
    exact (interfaceEndpoint_reachable_and_unreachable hb).2 huFramed
  rw [mem_squareRectangleVertices_iff]
  change 0 ≤ r 0 ∧ r 0 ≤ (m : ℤ) ∧ -(n : ℤ) ≤ r 1 ∧ r 1 ≤ (n : ℤ)
  omega

private theorem interfacePositiveEdge_endpoints_mem_rectangle_of_bond_not_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n
      (bondRectangleLeftReachableSet m n ω)) :
    b.base ∈ squareRectangleVertices m n ∧
      cubicStepFrom b.base (b.axis, true) ∈ squareRectangleVertices m n := by
  let eta := bondRectangleLeftReachableSet m n ω
  have hnoSite : eta ∉ siteSquareRectangleCrossingEvent m n :=
    bondRectangleLeftReachableSet_not_mem_siteCrossing_of_not_bondCrossing hno
  have hrRect := interfaceReachableEndpoint_mem_rectangle_of_bond_not_crossing hno hb
  have huBoundary :=
    interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hnoSite hb
  have huRect : siteRectangleInterfaceUnreachableEndpoint m n eta b ∈
      squareRectangleVertices m n :=
    (mem_siteRectangleLeftReachableBoundary_iff m n eta _).mp huBoundary |>.1
  by_cases hbase : siteRectangleFramedReachable m n eta b.base
  · simpa [eta, siteRectangleInterfaceReachableEndpoint,
      siteRectangleInterfaceUnreachableEndpoint, hbase] using And.intro hrRect huRect
  · simpa [eta, siteRectangleInterfaceReachableEndpoint,
      siteRectangleInterfaceUnreachableEndpoint, hbase] using And.intro huRect hrRect

private theorem interfaceReachableEndpoint_mem_bondReachable_of_not_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n
      (bondRectangleLeftReachableSet m n ω)) :
    siteRectangleInterfaceReachableEndpoint m n
        (bondRectangleLeftReachableSet m n ω) b ∈
      bondRectangleLeftReachableSet m n ω := by
  let eta := bondRectangleLeftReachableSet m n ω
  let r := siteRectangleInterfaceReachableEndpoint m n eta b
  have hrRect : r ∈ squareRectangleVertices m n :=
    interfaceReachableEndpoint_mem_rectangle_of_bond_not_crossing hno hb
  have hrOrdinary : r ∈ siteRectangleLeftReachableVertices m n eta :=
    (siteRectangleFramedReachable_iff_reachable_of_mem_rectangle hrRect).mp
      (interfaceEndpoint_reachable_and_unreachable hb).1
  rw [mem_siteRectangleLeftReachableVertices_iff] at hrOrdinary
  rcases hrOrdinary with ⟨_hrRect, _x, _hxLeft, w, _hwRect, hwEta⟩
  exact hwEta r w.end_mem_support

private theorem interfacePositiveEdge_vertical_base_strict_bounds_of_bond_not_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n
      (bondRectangleLeftReachableSet m n ω))
    (haxis : b.axis = (1 : Fin 2)) :
    0 < b.base 0 ∧ b.base 0 < (m : ℤ) := by
  let eta := bondRectangleLeftReachableSet m n ω
  let r := siteRectangleInterfaceReachableEndpoint m n eta b
  let u := siteRectangleInterfaceUnreachableEndpoint m n eta b
  have hend := interfacePositiveEdge_endpoints_mem_rectangle_of_bond_not_crossing hno hb
  have hbaseBounds := mem_squareRectangleVertices_iff.mp hend.1
  have hrEta : r ∈ eta :=
    interfaceReachableEndpoint_mem_bondReachable_of_not_crossing hno hb
  have hnoSite : eta ∉ siteSquareRectangleCrossingEvent m n :=
    bondRectangleLeftReachableSet_not_mem_siteCrossing_of_not_bondCrossing hno
  have huBoundary :=
    interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hnoSite hb
  have huRect : u ∈ squareRectangleVertices m n :=
    (mem_siteRectangleLeftReachableBoundary_iff m n eta u).mp huBoundary |>.1
  have hrRect : r ∈ squareRectangleVertices m n :=
    interfaceReachableEndpoint_mem_rectangle_of_bond_not_crossing hno hb
  have hrCoord : r 0 = b.base 0 := by
    by_cases hbase : siteRectangleFramedReachable m n eta b.base <;>
      simp [r, siteRectangleInterfaceReachableEndpoint, hbase, haxis,
        cubicStepFrom, cubicDirectionIncrement]
  have huCoord : u 0 = b.base 0 := by
    by_cases hbase : siteRectangleFramedReachable m n eta b.base <;>
      simp [u, siteRectangleInterfaceUnreachableEndpoint, hbase, haxis,
        cubicStepFrom, cubicDirectionIncrement]
  have hbaseNeZero : b.base 0 ≠ 0 := by
    intro hbZero
    have huLeft : u ∈ squareRectangleLeft m n := by
      rw [mem_squareRectangleLeft_iff]
      have huBounds := mem_squareRectangleVertices_iff.mp huRect
      exact ⟨huCoord.trans hbZero, huBounds.2.2.1, huBounds.2.2.2⟩
    have huEta : u ∈ eta :=
      mem_bondRectangleLeftReachableSet_of_mem_left huLeft
    have huOrdinary : u ∈ siteRectangleLeftReachableVertices m n eta :=
      mem_siteRectangleLeftReachableVertices_of_mem_left huLeft huEta
    exact (interfaceEndpoint_reachable_and_unreachable hb).2
      ((siteRectangleFramedReachable_iff_reachable_of_mem_rectangle huRect).mpr huOrdinary)
  have hbaseNeRight : b.base 0 ≠ (m : ℤ) := by
    intro hbRight
    have hrRight : r ∈ squareRectangleRight m n := by
      rw [mem_squareRectangleRight_iff]
      have hrBounds := mem_squareRectangleVertices_iff.mp hrRect
      exact ⟨hrCoord.trans hbRight, hrBounds.2.2.1, hrBounds.2.2.2⟩
    rcases hrEta with ⟨x, hxLeft, hxr⟩
    apply hno
    simp only [squareRectangleCrossingEvent, Set.mem_iUnion]
    exact ⟨x, hxLeft, r, hrRight, hxr⟩
  exact ⟨lt_of_le_of_ne hbaseBounds.1 (Ne.symm hbaseNeZero),
    lt_of_le_of_ne hbaseBounds.2.1 hbaseNeRight⟩

/-- A shifted-dual endpoint of the bond-reachability interface lies over one of the `m`
interior horizontal strips. -/
theorem interfaceDualVertex_horizontal_strict_bounds_of_bond_not_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n
      (bondRectangleLeftReachableSet m n ω))
    {z : DualSquareVertex}
    (hz : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex)) :
    0 ≤ z 0 ∧ z 0 < (m : ℤ) := by
  have hbCell := (mem_squareCellPositiveEdges_iff_mem_crossing).mpr hz
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at hbCell
  rcases hbCell with rfl | rfl | rfl | rfl
  · have hend := interfacePositiveEdge_endpoints_mem_rectangle_of_bond_not_crossing hno hb
    have hbase := mem_squareRectangleVertices_iff.mp hend.1
    have hstep := mem_squareRectangleVertices_iff.mp hend.2
    simp [squareVertex, cubicStepFrom, cubicDirectionIncrement] at hbase hstep ⊢
    omega
  · have hstrict :=
      interfacePositiveEdge_vertical_base_strict_bounds_of_bond_not_crossing hno hb rfl
    simp [squareVertex] at hstrict ⊢
    omega
  · have hend := interfacePositiveEdge_endpoints_mem_rectangle_of_bond_not_crossing hno hb
    have hbase := mem_squareRectangleVertices_iff.mp hend.1
    have hstep := mem_squareRectangleVertices_iff.mp hend.2
    simp [squareVertex, cubicStepFrom, cubicDirectionIncrement] at hbase hstep ⊢
    omega
  · have hstrict :=
      interfacePositiveEdge_vertical_base_strict_bounds_of_bond_not_crossing hno hb rfl
    simp [squareVertex] at hstrict
    exact ⟨hstrict.1.le, hstrict.2⟩

/-- Full coordinate bounds for a vertex incident to the bond-reachability interface. -/
theorem interfaceDualVertex_bounds_of_bond_not_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n
      (bondRectangleLeftReachableSet m n ω))
    {z : DualSquareVertex}
    (hz : z ∈ (squarePositiveEdgeDualCrossingEmbedding b : Sym2 DualSquareVertex)) :
    0 ≤ z 0 ∧ z 0 < (m : ℤ) ∧ -(n : ℤ) - 1 ≤ z 1 ∧ z 1 ≤ (n : ℤ) := by
  have hx := interfaceDualVertex_horizontal_strict_bounds_of_bond_not_crossing hno hb hz
  rcases mem_cells_or_bottom_or_top_of_mem_interface_incident hb hz with
    hzCell | hzBottom | hzTop
  · rw [mem_siteRectangleInterfaceCells_iff] at hzCell
    exact ⟨hx.1, hx.2, by omega, by omega⟩
  · exact ⟨hx.1, hx.2, by omega, by omega⟩
  · exact ⟨hx.1, hx.2, by omega, by omega⟩

/-- Every primal edge crossed by the bond-reachability interface is closed. -/
theorem not_edgeOpen_of_mem_bondRectangleInterfacePositiveEdges
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {b : SquarePositiveEdge}
    (hb : b ∈ siteRectangleInterfacePositiveEdges m n
      (bondRectangleLeftReachableSet m n ω)) :
    b.toEdge ∉ ω := by
  let eta := bondRectangleLeftReachableSet m n ω
  let r := siteRectangleInterfaceReachableEndpoint m n eta b
  let u := siteRectangleInterfaceUnreachableEndpoint m n eta b
  have hnoSite : eta ∉ siteSquareRectangleCrossingEvent m n :=
    bondRectangleLeftReachableSet_not_mem_siteCrossing_of_not_bondCrossing hno
  have hrRect : r ∈ squareRectangleVertices m n :=
    interfaceReachableEndpoint_mem_rectangle_of_bond_not_crossing hno hb
  have huBoundary :=
    interfaceUnreachableEndpoint_mem_reachableBoundary_of_not_crossing hnoSite hb
  have huRect : u ∈ squareRectangleVertices m n :=
    (mem_siteRectangleLeftReachableBoundary_iff m n eta u).mp huBoundary |>.1
  have hrOrdinary : r ∈ siteRectangleLeftReachableVertices m n eta :=
    (siteRectangleFramedReachable_iff_reachable_of_mem_rectangle hrRect).mp
      (interfaceEndpoint_reachable_and_unreachable hb).1
  have hrEta : r ∈ eta := by
    rw [mem_siteRectangleLeftReachableVertices_iff] at hrOrdinary
    rcases hrOrdinary with ⟨_hrRect, _x, _hxLeft, w, _hwRect, hwEta⟩
    exact hwEta r w.end_mem_support
  intro hbOpen
  have hruAdj : squareGraph.Adj r u := interfaceEndpoint_adj m n eta b
  have hedgeEq :
      (⟨s(r, u), (SimpleGraph.mem_edgeSet squareGraph).mpr hruAdj⟩ : SquareEdge) =
        b.toEdge := by
    apply Subtype.ext
    by_cases hbase : siteRectangleFramedReachable m n eta b.base
    · simp [r, u, siteRectangleInterfaceReachableEndpoint,
        siteRectangleInterfaceUnreachableEndpoint, hbase, SquarePositiveEdge.toEdge]
    · simp [r, u, siteRectangleInterfaceReachableEndpoint,
        siteRectangleInterfaceUnreachableEndpoint, hbase, SquarePositiveEdge.toEdge,
        Sym2.eq_swap]
  have hruOpen :
      (⟨s(r, u), (SimpleGraph.mem_edgeSet squareGraph).mpr hruAdj⟩ : SquareEdge) ∈ ω := by
    rwa [hedgeEq]
  have huEta : u ∈ eta :=
    bondRectangleLeftReachableSet_step hrEta hrRect huRect hruAdj hruOpen
  have huOrdinary : u ∈ siteRectangleLeftReachableVertices m n eta :=
    siteRectangleLeftReachableVertices_step hrOrdinary hruAdj huRect huEta
  exact (interfaceEndpoint_reachable_and_unreachable hb).2
    ((siteRectangleFramedReachable_iff_reachable_of_mem_rectangle huRect).mpr huOrdinary)

/-- Regard an interface-graph walk as a shifted-dual square-lattice walk. -/
noncomputable def bondRectangleInterfaceDualGraphWalk
    {m n : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (w : (siteRectangleInterfaceDualGraph m n
      (bondRectangleLeftReachableSet m n ω)).Walk u v) :
    dualSquareGraph.Walk u v :=
  w.map (SimpleGraph.Hom.ofLE
    (siteRectangleInterfaceDualGraph_le_dualSquareGraph m n
      (bondRectangleLeftReachableSet m n ω)))

/-- Under bond-crossing failure, every walk in the finite interface graph is dual-open. -/
theorem dualWalkIsOpen_bondRectangleInterfaceDualGraphWalk_of_not_crossing
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n)
    {u v : DualSquareVertex}
    (w : (siteRectangleInterfaceDualGraph m n
      (bondRectangleLeftReachableSet m n ω)).Walk u v) :
    dualWalkIsOpen ω (bondRectangleInterfaceDualGraphWalk w) := by
  intro e he
  let ed : DualSquareEdge :=
    ⟨e, (bondRectangleInterfaceDualGraphWalk w).edges_subset_edgeSet he⟩
  have heOriginal : e ∈ w.edges := by
    let F := SimpleGraph.Hom.ofLE
      (siteRectangleInterfaceDualGraph_le_dualSquareGraph m n
        (bondRectangleLeftReachableSet m n ω))
    change e ∈ (w.map F).edges at he
    rw [SimpleGraph.Walk.edges_map] at he
    rcases List.mem_map.mp he with ⟨f, hf, hfe⟩
    have hfe' : f = e := by
      simpa [F] using hfe
    simpa [hfe'] using hf
  have heGraph : e ∈
      (siteRectangleInterfaceDualGraph m n
        (bondRectangleLeftReachableSet m n ω)).edgeSet :=
    w.edges_subset_edgeSet heOriginal
  rw [mem_siteRectangleInterfaceDualGraph_edgeSet_iff] at heGraph
  rcases heGraph with ⟨heDual, heInterface⟩
  rw [mem_siteRectangleInterfaceDualEdges_iff] at heInterface
  rcases heInterface with ⟨b, hb, hbeq⟩
  have hedEq : ed = squarePositiveEdgeDualCrossingEmbedding b := by
    apply Subtype.ext
    exact (congrArg Subtype.val hbeq).symm
  rw [show (⟨e, (bondRectangleInterfaceDualGraphWalk w).edges_subset_edgeSet he⟩ :
      DualSquareEdge) = ed by rfl, hedEq, dualSquareConfiguration_open_iff,
    squareEdgeDualCrossingEquiv_symm_squarePositiveEdgeDualCrossingEmbedding]
  exact not_edgeOpen_of_mem_bondRectangleInterfacePositiveEdges hno hb

/-- Deterministic bond crossing alternative for the centered rectangle: if there is no open
left--right crossing, there is a dual-open shifted-lattice walk from the exterior bottom row to
the exterior top row. -/
theorem exists_dualOpen_walk_bottom_top_of_not_squareRectangleCrossing
    {m n : ℕ} (hn : 0 < n) {ω : EdgeConfiguration 2}
    (hno : ω ∉ squareRectangleCrossingEvent m n) :
    ∃ b t : DualSquareVertex,
      b ∈ siteRectangleBottomInterfaceDualVertices m n
          (bondRectangleLeftReachableSet m n ω) ∧
        t ∈ siteRectangleTopInterfaceDualVertices m n
          (bondRectangleLeftReachableSet m n ω) ∧
          ∃ w : dualSquareGraph.Walk b t, dualWalkIsOpen ω w := by
  rcases exists_interfaceDual_reachable_bottom_top
      (m := m) (n := n) (eta := bondRectangleLeftReachableSet m n ω) hn with
    ⟨b, hb, t, ht, hbt⟩
  let w := Classical.choice hbt
  exact ⟨b, t, hb, ht, bondRectangleInterfaceDualGraphWalk w,
    dualWalkIsOpen_bondRectangleInterfaceDualGraphWalk_of_not_crossing hno w⟩

end Percolation
