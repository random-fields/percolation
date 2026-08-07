import Percolation.Planar.TriangularPeierlsRay

/-!
# Normalizing a triangular Peierls contour on the positive ray

The positive-ray cycle selected by finite parity also crosses the negative horizontal ray.  This
normalizes it at a positive coordinate strictly smaller than its length, matching the finite
families counted in `TriangularHexCounting`.
-/

namespace Percolation

open SimpleGraph
open scoped Sym2

noncomputable section

/-- A hexagonal face lies on the upper side of the horizontal primal axis when its anchor has
nonnegative second coordinate. -/
def triangularHexAboveAxis (z : TriangularHexVertex) : Prop :=
  0 ≤ z.1 1

/-- An unordered hexagonal edge changes sides of the horizontal primal axis. -/
def triangularHexAxisCutEdge (e : Sym2 TriangularHexVertex) : Prop :=
  ∃ x y : TriangularHexVertex, e = s(x, y) ∧
    ¬ (triangularHexAboveAxis x ↔ triangularHexAboveAxis y)

local instance : DecidablePred triangularHexAxisCutEdge :=
  Classical.decPred _

theorem triangularHexAxisCutEdge_mk_iff (x y : TriangularHexVertex) :
    triangularHexAxisCutEdge s(x, y) ↔
      ¬ (triangularHexAboveAxis x ↔ triangularHexAboveAxis y) := by
  constructor
  · rintro ⟨a, b, hab, hcut⟩
    rcases Sym2.eq_iff.mp hab with hs | hs
    · rcases hs with ⟨hbx, hay⟩
      subst b
      subst a
      tauto
    · rcases hs with ⟨hax, hby⟩
      subst a
      subst b
      tauto
  · intro h
    exact ⟨x, y, rfl, h⟩

/-- Parity of side changes along a walk is determined by the sides of its endpoints. -/
theorem odd_countP_triangularHexAxisCutEdge_iff
    {u v : TriangularHexVertex} (w : triangularHexGraph.Walk u v) :
    Odd (w.edges.countP fun e ↦ decide (triangularHexAxisCutEdge e)) ↔
      ¬ (triangularHexAboveAxis u ↔ triangularHexAboveAxis v) := by
  induction w with
  | nil => simp
  | @cons u x v hux w ih =>
      by_cases hu : triangularHexAboveAxis u <;>
        by_cases hx : triangularHexAboveAxis x <;>
          by_cases hv : triangularHexAboveAxis v <;>
            simp_all [triangularHexAxisCutEdge_mk_iff, Nat.odd_add]

/-- A closed trail uses an even number of horizontal-axis crossing edges. -/
theorem even_card_filter_triangularHexAxisCutEdge_of_isCycle
    {u : TriangularHexVertex} {w : triangularHexGraph.Walk u u}
    (hw : w.IsCycle) :
    Even ((w.edges.toFinset.filter triangularHexAxisCutEdge).card) := by
  classical
  have hcard : (w.edges.toFinset.filter triangularHexAxisCutEdge).card =
      w.edges.countP (fun e ↦ decide (triangularHexAxisCutEdge e)) := by
    rw [show w.edges.toFinset.filter triangularHexAxisCutEdge =
        (w.edges.filter fun e ↦ decide (triangularHexAxisCutEdge e)).toFinset by
      ext e
      simp]
    rw [List.toFinset_card_of_nodup (hw.isTrail.edges_nodup.filter _)]
    rw [← List.countP_eq_length_filter]
  rw [hcard, ← Nat.not_odd_iff_even]
  intro hodd
  exact (odd_countP_triangularHexAxisCutEdge_iff w).mp hodd Iff.rfl

/-- The signed horizontal dual edge at primal coordinate `a`. -/
def triangularHorizontalAxisDualEdge (a : ℤ) : Sym2 TriangularHexVertex :=
  triangularHexDartEdge (squareVertex a 0, false) 1

@[simp]
theorem triangularHorizontalAxisDualEdge_nat (k : ℕ) :
    triangularHorizontalAxisDualEdge k = triangularPositiveRayDualEdge k := by
  rfl

theorem triangularHorizontalAxisDualEdge_axisCut (a : ℤ) :
    triangularHexAxisCutEdge (triangularHorizontalAxisDualEdge a) := by
  rw [triangularHorizontalAxisDualEdge, triangularHexDartEdge,
    triangularHexAxisCutEdge_mk_iff]
  simp [triangularHexAboveAxis, triangularHexNeighbor, squareVertex]

/-- Every hexagonal edge crossing the horizontal axis has a unique signed horizontal
coordinate. -/
theorem exists_eq_triangularHorizontalAxisDualEdge_of_axisCut
    {e : Sym2 TriangularHexVertex} (he : e ∈ triangularHexGraph.edgeSet)
    (hcut : triangularHexAxisCutEdge e) :
    ∃ a : ℤ, e = triangularHorizontalAxisDualEdge a := by
  have hadj : triangularHexGraph.Adj e.out.1 e.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    simpa only [e.out_eq] using he
  rcases (triangularHexGraph_adj_iff e.out.1 e.out.2).mp hadj with ⟨k, hk⟩
  let z := e.out.1
  have heDart : e = triangularHexDartEdge z k := by
    dsimp only [z]
    rw [triangularHexDartEdge, ← hk]
    exact e.out_eq.symm
  rw [heDart, triangularHexDartEdge,
    triangularHexAxisCutEdge_mk_iff] at hcut
  rcases z with ⟨x, b⟩
  fin_cases k <;> cases b
  · simp [triangularHexAboveAxis, triangularHexNeighbor] at hcut
  · simp [triangularHexAboveAxis, triangularHexNeighbor] at hcut
  · refine ⟨x 0, heDart.trans ?_⟩
    simp [triangularHorizontalAxisDualEdge, triangularHexDartEdge,
      triangularHexNeighbor, triangularHexAboveAxis] at hcut ⊢
    constructor <;> funext i <;> fin_cases i <;>
      simp [squareVertex] <;> omega
  · refine ⟨x 0, heDart.trans ?_⟩
    simp [triangularHorizontalAxisDualEdge, triangularHexDartEdge,
      triangularHexNeighbor, triangularHexAboveAxis] at hcut ⊢
    constructor <;> funext i <;> fin_cases i <;>
      simp [squareVertex] <;> omega
  · simp [triangularHexAboveAxis, triangularHexNeighbor] at hcut
  · simp [triangularHexAboveAxis, triangularHexNeighbor] at hcut

/-- One dual step changes the first anchor coordinate by at most one. -/
theorem abs_triangularHexNeighbor_first_sub_le_one
    (z : TriangularHexVertex) (k : Fin 3) :
    |(triangularHexNeighbor z k).1 0 - z.1 0| ≤ 1 := by
  rcases z with ⟨x, b⟩
  fin_cases k <;> cases b <;>
    simp [triangularHexNeighbor, squareVertex, abs_of_nonneg, abs_of_nonpos]

/-- Anchor-coordinate displacement is bounded by walk length. -/
theorem abs_triangularHexWalk_first_sub_le_length
    {u v : TriangularHexVertex} (w : triangularHexGraph.Walk u v) :
    |v.1 0 - u.1 0| ≤ (w.length : ℤ) := by
  induction w with
  | nil => simp
  | @cons u x v hux w ih =>
      rcases (triangularHexGraph_adj_iff u x).mp hux with ⟨k, rfl⟩
      have hstep := abs_triangularHexNeighbor_first_sub_le_one u k
      have htriangle :
          |v.1 0 - u.1 0| ≤
            |v.1 0 - (triangularHexNeighbor u k).1 0| +
              |(triangularHexNeighbor u k).1 0 - u.1 0| := by
        simpa [sub_eq_add_neg, add_assoc] using
          abs_add_le (v.1 0 - (triangularHexNeighbor u k).1 0)
            ((triangularHexNeighbor u k).1 0 - u.1 0)
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- Every vertex in a walk lies within its length of the starting anchor coordinate. -/
theorem abs_triangularHexWalk_support_first_sub_le_length
    {u v z : TriangularHexVertex} (w : triangularHexGraph.Walk u v)
    (hz : z ∈ w.support) :
    |z.1 0 - u.1 0| ≤ (w.length : ℤ) := by
  have hwalk := abs_triangularHexWalk_first_sub_le_length (w.takeUntil z hz)
  exact hwalk.trans (by exact_mod_cast w.length_takeUntil_le hz)

/-- The boundary graph is a spanning subgraph of the full hexagonal dual. -/
theorem triangularHexBoundaryGraph_le_triangularHexGraph
    (C : Set SquareVertex) :
    triangularHexBoundaryGraph C ≤ triangularHexGraph := by
  intro x y hxy
  rcases (triangularHexBoundaryGraph_adj_iff C x y).mp hxy with ⟨k, rfl, _⟩
  exact triangularHexGraph_adj_neighbor x k

/-- A finite primal set containing the origin has a boundary cycle normalized at a positive-ray
vertex whose coordinate is strictly smaller than the cycle length.  The selected positive-ray
edge and every edge of the normalized cycle remain boundary edges. -/
theorem exists_positiveRayRootedTriangularHexBoundaryCycle
    {C : Set SquareVertex} (hC : C.Finite)
    (hzero : triangularPositiveRayPrimalVertex 0 ∈ C) :
    ∃ n : ℕ, ∃ c : PositiveRayRootedTriangularHexCycle n,
      3 ≤ n ∧
        triangularPositiveRayDualEdge (c.1 : ℕ) ∈ c.2.1.edges ∧
          ∀ e ∈ c.2.1.edges, e ∈ (triangularHexBoundaryGraph C).edgeSet := by
  classical
  obtain ⟨R, hRoutside, u, w, hwcycle, hwodd⟩ :=
    exists_triangularHexBoundary_isCycle_odd_positiveRay hC hzero
  let X := (triangularPositiveRayBoundaryEdges C R).filter
    (fun e ↦ e ∈ w.edges.toFinset)
  have hXpos : 0 < X.card := by
    apply Nat.pos_of_ne_zero
    intro hzeroCard
    rw [hzeroCard] at hwodd
    simp at hwodd
  obtain ⟨e, heX⟩ := Finset.card_pos.mp hXpos
  have heX' : e ∈ triangularPositiveRayBoundaryEdges C R ∧
      e ∈ w.edges.toFinset := by
    simpa [X] using heX
  rw [triangularPositiveRayBoundaryEdges, Finset.mem_map] at heX'
  obtain ⟨k, hkchange, hek⟩ := heX'.1
  have heq : e = triangularPositiveRayDualEdge k := by
    simpa using hek.symm
  have hkW : triangularPositiveRayDualEdge k ∈ w.edges := by
    simpa [heq] using heX'.2
  let q : triangularHexGraph.Walk u u :=
    w.mapLe (triangularHexBoundaryGraph_le_triangularHexGraph C)
  have hqcycle : q.IsCycle :=
    hwcycle.mapLe (triangularHexBoundaryGraph_le_triangularHexGraph C)
  have hqedges : q.edges = w.edges :=
    w.edges_mapLe_eq_edges (triangularHexBoundaryGraph_le_triangularHexGraph C)
  have hkQ : triangularPositiveRayDualEdge k ∈ q.edges := by
    simpa [hqedges] using hkW
  have hkSupport : triangularHexPositiveRayVertex k ∈ q.support := by
    apply q.fst_mem_support_of_mem_edges
    simpa [triangularPositiveRayDualEdge, triangularHexDartEdge] using hkQ
  have haxisEven : Even ((q.edges.toFinset.filter triangularHexAxisCutEdge).card) :=
    even_card_filter_triangularHexAxisCutEdge_of_isCycle hqcycle
  have hnegative : ∃ a : ℤ, a < 0 ∧
      triangularHorizontalAxisDualEdge a ∈ q.edges.toFinset := by
    by_contra hno
    push Not at hno
    have hfinset : q.edges.toFinset.filter triangularHexAxisCutEdge = X := by
      ext d
      constructor
      · intro hd
        rw [Finset.mem_filter] at hd
        obtain ⟨a, hda⟩ :=
          exists_eq_triangularHorizontalAxisDualEdge_of_axisCut
            (q.edges_subset_edgeSet (by simpa using hd.1)) hd.2
        have ha : 0 ≤ a := by
          by_contra ha
          exact hno a (lt_of_not_ge ha) (by simpa [hda] using hd.1)
        let j : ℕ := a.toNat
        have hja : (j : ℤ) = a := by
          simpa [j] using (Int.toNat_of_nonneg ha)
        have hdj : d = triangularPositiveRayDualEdge j := by
          rw [hda, ← hja, triangularHorizontalAxisDualEdge_nat]
        have hjBoundary : triangularPositiveRayDualEdge j ∈
            (triangularHexBoundaryGraph C).edgeSet := by
          apply w.edges_subset_edgeSet
          rw [← hqedges]
          simpa [hdj] using hd.1
        have hjChange := mem_triangularPositiveRayChangeIndices_of_mem_boundary
          hRoutside hjBoundary
        rw [Finset.mem_filter]
        refine ⟨?_, by simpa [← hqedges, hdj] using hd.1⟩
        rw [triangularPositiveRayBoundaryEdges, Finset.mem_map]
        refine ⟨j, hjChange, ?_⟩
        rw [hdj]
        rfl
      · intro hd
        rw [Finset.mem_filter] at hd ⊢
        refine ⟨by simpa [hqedges] using hd.2, ?_⟩
        rw [triangularPositiveRayBoundaryEdges, Finset.mem_map] at hd
        obtain ⟨j, _hj, hdj⟩ := hd.1
        simpa [← hdj] using triangularHorizontalAxisDualEdge_axisCut (j : ℤ)
    rw [hfinset] at haxisEven
    exact (Nat.not_odd_iff_even.mpr haxisEven) hwodd
  obtain ⟨a, ha, haEdge⟩ := hnegative
  have haSupport : (squareVertex a 0, false) ∈ q.support := by
    apply q.fst_mem_support_of_mem_edges
    simpa [triangularHorizontalAxisDualEdge, triangularHexDartEdge] using haEdge
  let cwalk := q.rotate (triangularHexPositiveRayVertex k) hkSupport
  have hacwalk : (squareVertex a 0, false) ∈ cwalk.support := by
    simpa [cwalk] using
      (q.mem_support_rotate_iff (triangularHexPositiveRayVertex k) hkSupport).2 haSupport
  have hdist := abs_triangularHexWalk_support_first_sub_le_length cwalk hacwalk
  have hkle : k < cwalk.length := by
    have hdistq : |a - (k : ℤ)| ≤ (q.length : ℤ) := by
      simpa [cwalk, triangularHexPositiveRayVertex, squareVertex] using hdist
    have hsign : a - (k : ℤ) ≤ 0 := by omega
    rw [abs_of_nonpos hsign] at hdistq
    have hkq : k < q.length := by omega
    simpa [cwalk] using hkq
  let n := cwalk.length
  let c : PositiveRayRootedTriangularHexCycle n :=
    ⟨⟨k, by simpa [n] using hkle⟩,
      ⟨cwalk, hqcycle.rotate hkSupport, rfl⟩⟩
  refine ⟨n, c, ?_, ?_, ?_⟩
  · simpa [n, cwalk] using hqcycle.three_le_length
  · change triangularPositiveRayDualEdge k ∈ cwalk.edges
    exact (q.rotate_edges _ _).perm.mem_iff.mpr hkQ
  · intro d hd
    apply w.edges_subset_edgeSet
    rw [← hqedges]
    exact (q.rotate_edges _ _).perm.mem_iff.mp hd

end

end Percolation
