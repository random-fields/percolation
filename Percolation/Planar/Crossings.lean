import Percolation.Bernoulli.DisjointConnections
import Percolation.Critical.BoxRadius

/-!
# Finite square-lattice crossing events

This file supplies the finite rectangle vocabulary used in Grimmett's forward references from
Chapter 7 to Chapter 11.  Rectangles are represented by explicit vertex and edge finsets, so all
crossing events are finite cylinders and can be used directly with sprinkling and Russo theory.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- The integer rectangle `[0, m] × [-n, n]` in the square lattice. -/
noncomputable def squareRectangleVertices (m n : ℕ) : Finset SquareVertex :=
  Fintype.piFinset fun i : Fin 2 ↦
    if i = 0 then Finset.Icc 0 (m : ℤ) else Finset.Icc (-(n : ℤ)) (n : ℤ)

@[simp]
theorem mem_squareRectangleVertices_iff {m n : ℕ} {x : SquareVertex} :
    x ∈ squareRectangleVertices m n ↔
      0 ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  classical
  simp only [squareRectangleVertices, Fintype.mem_piFinset]
  constructor
  · intro h
    have h₀ : 0 ≤ x 0 ∧ x 0 ≤ (m : ℤ) := by
      simpa [Finset.mem_Icc] using h (0 : Fin 2)
    have h₁ : -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
      simpa [Finset.mem_Icc] using h (1 : Fin 2)
    exact ⟨h₀.1, h₀.2, h₁.1, h₁.2⟩
  · rintro ⟨hx₀, hx₀', hx₁, hx₁'⟩ i
    fin_cases i
    · simp [hx₀, hx₀']
    · simp [hx₁, hx₁']

/-- The left side of `[0, m] × [-n,n]`. -/
noncomputable def squareRectangleLeft (m n : ℕ) : Finset SquareVertex :=
  (squareRectangleVertices m n).filter fun x ↦ x 0 = 0

/-- The right side of `[0, m] × [-n,n]`. -/
noncomputable def squareRectangleRight (m n : ℕ) : Finset SquareVertex :=
  (squareRectangleVertices m n).filter fun x ↦ x 0 = (m : ℤ)

@[simp]
theorem mem_squareRectangleLeft_iff {m n : ℕ} {x : SquareVertex} :
    x ∈ squareRectangleLeft m n ↔
      x 0 = 0 ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  classical
  simp only [squareRectangleLeft, Finset.mem_filter, mem_squareRectangleVertices_iff]
  omega

@[simp]
theorem mem_squareRectangleRight_iff {m n : ℕ} {x : SquareVertex} :
    x ∈ squareRectangleRight m n ↔
      x 0 = (m : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ (n : ℤ) := by
  classical
  simp only [squareRectangleRight, Finset.mem_filter, mem_squareRectangleVertices_iff]
  omega

/-- All square-lattice edges whose two endpoints lie in `[0,m] × [-n,n]`. -/
noncomputable def squareRectangleEdges (m n : ℕ) : Finset SquareEdge := by
  classical
  exact (cubicBoxEdges 2 cubicOrigin (max m n)).filter fun e ↦
    e.1.out.1 ∈ squareRectangleVertices m n ∧
      e.1.out.2 ∈ squareRectangleVertices m n

theorem endpoint_mem_squareRectangle_of_edge_mem {m n : ℕ} {e : SquareEdge}
    (he : e ∈ squareRectangleEdges m n) {x : SquareVertex}
    (hx : x ∈ (e : Sym2 SquareVertex)) : x ∈ squareRectangleVertices m n := by
  classical
  have hend := (Finset.mem_filter.mp he).2
  rw [← e.1.out_eq] at hx
  change x ∈ s(e.1.out.1, e.1.out.2) at hx
  rw [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact hend.1
  · exact hend.2

/-- An open left-right crossing of `[0,m] × [-n,n]`. -/
def squareRectangleCrossingEvent (m n : ℕ) : Set (EdgeConfiguration 2) :=
  ⋃ x ∈ squareRectangleLeft m n, ⋃ y ∈ squareRectangleRight m n,
    connectionEventIn 2 (squareRectangleEdges m n) x y

theorem measurableSet_squareRectangleCrossingEvent (m n : ℕ) :
    MeasurableSet (squareRectangleCrossingEvent m n) := by
  apply (squareRectangleLeft m n).measurableSet_biUnion
  intro x _hx
  apply (squareRectangleRight m n).measurableSet_biUnion
  intro y _hy
  exact (dependsOn_connectionEventIn 2 (squareRectangleEdges m n) x y).measurableSet

theorem isIncreasingEvent_squareRectangleCrossingEvent (m n : ℕ) :
    IsIncreasingEvent (squareRectangleCrossingEvent m n) := by
  intro ω η hωη hω
  simp only [squareRectangleCrossingEvent, Set.mem_iUnion] at hω ⊢
  obtain ⟨x, _hx, y, _hy, hxy⟩ := hω
  exact ⟨x, _hx, y, _hy,
    isIncreasingEvent_connectionEventIn 2 (squareRectangleEdges m n) x y hωη hxy⟩

theorem dependsOn_squareRectangleCrossingEvent (m n : ℕ) :
    DependsOn (squareRectangleEdges m n) (squareRectangleCrossingEvent m n) := by
  intro ω η hagree
  constructor
  · intro hω
    simp only [squareRectangleCrossingEvent, Set.mem_iUnion] at hω ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hω
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (squareRectangleEdges m n) x y hagree).mp hxy⟩
  · intro hη
    simp only [squareRectangleCrossingEvent, Set.mem_iUnion] at hη ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hη
    exact ⟨x, hx, y, hy,
      (dependsOn_connectionEventIn 2 (squareRectangleEdges m n) x y hagree).mpr hxy⟩

@[simp]
theorem squareRectangleCrossingEvent_zero_left (n : ℕ) :
    squareRectangleCrossingEvent 0 n = Set.univ := by
  ext ω
  constructor
  · simp
  · intro _h
    let x : SquareVertex := squareVertex 0 0
    have hxL : x ∈ squareRectangleLeft 0 n := by simp [x, cubicOrigin]
    have hxR : x ∈ squareRectangleRight 0 n := by simp [x, cubicOrigin]
    simp only [squareRectangleCrossingEvent, Set.mem_iUnion]
    refine ⟨x, hxL, x, hxR, SimpleGraph.Walk.nil, ?_, ?_⟩
    · simp [walkIsOpen]
    · intro e he
      simp [walkEdgeFinset, walkEdgeList] at he

/-! ### Families of edge-disjoint crossings -/

/-- A chosen open left-right crossing of a square-lattice rectangle. -/
structure OpenSquareRectangleCrossing (m n : ℕ) (ω : EdgeConfiguration 2) where
  start : SquareVertex
  finish : SquareVertex
  walk : squareGraph.Walk start finish
  start_mem : start ∈ squareRectangleLeft m n
  finish_mem : finish ∈ squareRectangleRight m n
  isOpen : walkIsOpen ω walk
  edges_subset : walkEdgeFinset walk ⊆ squareRectangleEdges m n

/-- There are `k` pairwise edge-disjoint open left-right crossings of the rectangle. -/
def HasEdgeDisjointSquareRectangleCrossings (m n k : ℕ) (ω : EdgeConfiguration 2) : Prop :=
  ∃ C : Fin k → OpenSquareRectangleCrossing m n ω,
    Pairwise fun i j ↦ Disjoint (walkEdgeFinset (C i).walk) (walkEdgeFinset (C j).walk)

theorem hasEdgeDisjointSquareRectangleCrossings_zero (m n : ℕ)
    (ω : EdgeConfiguration 2) : HasEdgeDisjointSquareRectangleCrossings m n 0 ω := by
  refine ⟨Fin.elim0, ?_⟩
  intro i
  exact Fin.elim0 i

private theorem OpenSquareRectangleCrossing.start_ne_finish {m n : ℕ}
    (hm : 1 ≤ m) {ω : EdgeConfiguration 2} (C : OpenSquareRectangleCrossing m n ω) :
    C.start ≠ C.finish := by
  intro h
  have hs := (mem_squareRectangleLeft_iff.mp C.start_mem).1
  have ht := (mem_squareRectangleRight_iff.mp C.finish_mem).1
  rw [h] at hs
  omega

private theorem OpenSquareRectangleCrossing.edgeFinset_nonempty {m n : ℕ}
    (hm : 1 ≤ m) {ω : EdgeConfiguration 2} (C : OpenSquareRectangleCrossing m n ω) :
    (walkEdgeFinset C.walk).Nonempty := by
  have hn : ¬ C.walk.Nil := SimpleGraph.Walk.not_nil_of_ne (C.start_ne_finish hm)
  have hedges : C.walk.edges ≠ [] := SimpleGraph.Walk.edges_eq_nil.not.mpr hn
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil C.walk.edges hedges
  let e' : SquareEdge := ⟨e, C.walk.edges_subset_edgeSet he⟩
  exact ⟨e', (mem_walkEdgeFinset_iff C.walk e').mpr he⟩

/-- A family of edge-disjoint crossings cannot contain more members than the rectangle has
edges. -/
theorem hasEdgeDisjointSquareRectangleCrossings_le_edge_card {m n k : ℕ}
    (hm : 1 ≤ m) {ω : EdgeConfiguration 2}
    (h : HasEdgeDisjointSquareRectangleCrossings m n k ω) :
    k ≤ (squareRectangleEdges m n).card := by
  classical
  obtain ⟨C, hC⟩ := h
  let chosen : ∀ i : Fin k, SquareEdge := fun i ↦
    Classical.choose ((C i).edgeFinset_nonempty hm)
  have chosen_mem (i : Fin k) : chosen i ∈ walkEdgeFinset (C i).walk :=
    Classical.choose_spec ((C i).edgeFinset_nonempty hm)
  let f : Fin k → {e // e ∈ squareRectangleEdges m n} := fun i ↦
    ⟨chosen i, (C i).edges_subset (chosen_mem i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hd := hC hne
    have heq : chosen i = chosen j := Subtype.ext_iff.mp hij
    exact Finset.disjoint_left.mp hd (chosen_mem i) (heq ▸ chosen_mem j)
  simpa [f] using Fintype.card_le_of_injective f hf

/-- The maximal number of edge-disjoint open left-right crossings.  The source denotes this
quantity by `M_{n+1}` in Lemma 11.22 and by `A_r` in Theorem 7.68. -/
noncomputable def maxEdgeDisjointSquareRectangleCrossings
    (m n : ℕ) (ω : EdgeConfiguration 2) : ℕ := by
  classical
  exact if m = 0 then 0 else
    Nat.findGreatest (fun k ↦ HasEdgeDisjointSquareRectangleCrossings m n k ω)
      (squareRectangleEdges m n).card

@[simp]
theorem maxEdgeDisjointSquareRectangleCrossings_zero_left (n : ℕ)
    (ω : EdgeConfiguration 2) :
    maxEdgeDisjointSquareRectangleCrossings 0 n ω = 0 := by
  simp [maxEdgeDisjointSquareRectangleCrossings]

theorem hasEdgeDisjointSquareRectangleCrossings_max (m n : ℕ) (hm : 1 ≤ m)
    (ω : EdgeConfiguration 2) :
    HasEdgeDisjointSquareRectangleCrossings m n
      (maxEdgeDisjointSquareRectangleCrossings m n ω) ω := by
  classical
  rw [maxEdgeDisjointSquareRectangleCrossings, if_neg (Nat.ne_of_gt hm)]
  exact Nat.findGreatest_spec
    (P := fun k ↦ HasEdgeDisjointSquareRectangleCrossings m n k ω)
    (m := 0) (Nat.zero_le _) <|
    hasEdgeDisjointSquareRectangleCrossings_zero m n ω

theorem hasEdgeDisjointSquareRectangleCrossings_iff_le_max {m n k : ℕ}
    (hm : 1 ≤ m) (ω : EdgeConfiguration 2) :
    HasEdgeDisjointSquareRectangleCrossings m n k ω ↔
      k ≤ maxEdgeDisjointSquareRectangleCrossings m n ω := by
  classical
  constructor
  · intro hk
    by_contra hnot
    have hlt : maxEdgeDisjointSquareRectangleCrossings m n ω < k := Nat.lt_of_not_ge hnot
    rw [maxEdgeDisjointSquareRectangleCrossings, if_neg (Nat.ne_of_gt hm)] at hlt
    exact (Nat.findGreatest_is_greatest
      (P := fun j ↦ HasEdgeDisjointSquareRectangleCrossings m n j ω) hlt
      (hasEdgeDisjointSquareRectangleCrossings_le_edge_card hm hk)) hk
  · intro hk
    obtain ⟨C, hC⟩ := hasEdgeDisjointSquareRectangleCrossings_max m n hm ω
    let ι : Fin k → Fin (maxEdgeDisjointSquareRectangleCrossings m n ω) :=
      Fin.castLE hk
    refine ⟨fun i ↦ C (ι i), ?_⟩
    intro i j hij
    apply hC
    intro heq
    exact hij (Fin.castLE_injective hk heq)

@[simp]
theorem maxEdgeDisjointSquareRectangleCrossings_empty {m n : ℕ} (hm : 1 ≤ m) :
    maxEdgeDisjointSquareRectangleCrossings m n (∅ : EdgeConfiguration 2) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hone : HasEdgeDisjointSquareRectangleCrossings m n 1
      (∅ : EdgeConfiguration 2) :=
    (hasEdgeDisjointSquareRectangleCrossings_iff_le_max hm ∅).mpr hpos
  obtain ⟨C, _hC⟩ := hone
  let crossing := C (0 : Fin 1)
  obtain ⟨e, he⟩ := crossing.edgeFinset_nonempty hm
  have heEdges : e.1 ∈ crossing.walk.edges :=
    (mem_walkEdgeFinset_iff crossing.walk e).mp he
  exact crossing.isOpen e heEdges

end Percolation
