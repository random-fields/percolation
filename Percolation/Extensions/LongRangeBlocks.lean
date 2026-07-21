import Percolation.Extensions.LongRangePowerLawFamily
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Hierarchical blocks for one-dimensional long-range percolation

This is the deterministic half of the Newman--Schulman renormalization used for Grimmett
Theorem 12.8.  A level-zero block is retained when all of its nearest-neighbour bonds are open.
A parent retains the union of its retained children when sufficiently many children survive and
the surviving child clusters are joined in their natural order.  All choices are canonical and
finite, so later probability estimates can condition on literal finite traces.
-/

namespace Percolation

open scoped BigOperators

/-- Classical if-then-else without leaking a decidability argument through public block
interfaces. -/
noncomputable def longRangeClassicalIf {α : Sort*} (P : Prop) (yes no : α) : α := by
  classical
  exact if P then yes else no

/-- Length of a level-`k` block. -/
def longRangeBlockLength (base arity k : ℕ) : ℕ := base * arity ^ k

@[simp]
theorem longRangeBlockLength_zero (base arity : ℕ) :
    longRangeBlockLength base arity 0 = base := by
  simp [longRangeBlockLength]

theorem longRangeBlockLength_succ (base arity k : ℕ) :
    longRangeBlockLength base arity (k + 1) =
      arity * longRangeBlockLength base arity k := by
  rw [longRangeBlockLength, longRangeBlockLength, pow_succ]
  ac_rfl

/-- The aligned level-`k` block with coarse index `z`. -/
noncomputable def longRangeBlockVertices (base arity k : ℕ) (z : ℤ) : Finset ℤ :=
  Finset.Icc (z * longRangeBlockLength base arity k)
    (z * longRangeBlockLength base arity k + longRangeBlockLength base arity k - 1)

theorem longRangeBlockVertices_card (base arity k : ℕ) (z : ℤ) :
    (longRangeBlockVertices base arity k z).card =
      longRangeBlockLength base arity k := by
  rw [longRangeBlockVertices, Int.card_Icc]
  have heq :
      z * (longRangeBlockLength base arity k : ℤ) +
          (longRangeBlockLength base arity k : ℤ) - 1 + 1 -
          z * (longRangeBlockLength base arity k : ℤ) =
        (longRangeBlockLength base arity k : ℤ) := by ring
  rw [heq, Int.toNat_natCast]

theorem mem_longRangeBlockVertices_iff {base arity k : ℕ} {z x : ℤ} :
    x ∈ longRangeBlockVertices base arity k z ↔
      z * longRangeBlockLength base arity k ≤ x ∧
      x ≤ z * longRangeBlockLength base arity k +
        longRangeBlockLength base arity k - 1 := by
  simp [longRangeBlockVertices]

theorem longRangeBlockVertices_child_subset (base arity k : ℕ) (z : ℤ)
    {i : ℕ} (hi : i < arity) :
    longRangeBlockVertices base arity k (z * arity + i) ⊆
      longRangeBlockVertices base arity (k + 1) z := by
  intro x hx
  rw [mem_longRangeBlockVertices_iff] at hx ⊢
  rw [longRangeBlockLength_succ]
  have hL : 0 ≤ (longRangeBlockLength base arity k : ℤ) := by positivity
  have hi0 : 0 ≤ (i : ℤ) := by positivity
  have hiA : (i : ℤ) < arity := by exact_mod_cast hi
  push_cast at hx ⊢
  constructor <;> nlinarith [hx.1, hx.2]

theorem longRangeBlockVertices_children_disjoint
    {base arity k : ℕ} (hbase : 0 < base) (harity : 0 < arity) (z : ℤ)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (longRangeBlockVertices base arity k (z * arity + i))
      (longRangeBlockVertices base arity k (z * arity + j)) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_longRangeBlockVertices_iff] at hxi hxj
  have hL : 0 < longRangeBlockLength base arity k := by
    simp [longRangeBlockLength, hbase, harity]
  have hij' : i < j ∨ j < i := Nat.lt_or_gt_of_ne hij
  push_cast at hxi hxj
  rcases hij' with hij' | hij'
  · have hc : (i : ℤ) + 1 ≤ j := by exact_mod_cast hij'
    nlinarith
  · have hc : (j : ℤ) + 1 ≤ i := by exact_mod_cast hij'
    nlinarith

/-- Nearest-neighbour bonds internal to a finite integer block. -/
noncomputable def longRangeBlockNearestEdges (base arity k : ℕ) (z : ℤ) :
    Finset (Sym2 ℤ) :=
  ((longRangeBlockVertices base arity k z).filter fun x ↦
    x + 1 ∈ longRangeBlockVertices base arity k z).image fun x ↦ s(x, x + 1)

theorem mem_longRangeBlockNearestEdges_of_mem_succ
    {base arity k : ℕ} {z x : ℤ}
    (hx : x ∈ longRangeBlockVertices base arity k z)
    (hxs : x + 1 ∈ longRangeBlockVertices base arity k z) :
    s(x, x + 1) ∈ longRangeBlockNearestEdges base arity k z := by
  classical
  rw [longRangeBlockNearestEdges, Finset.mem_image]
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxs⟩, rfl⟩

/-- Two finite vertex sets have at least one configured bond between them. -/
def longRangeSetsLinked (ω : LongRangeConfiguration) (A B : Finset ℤ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, s(a, b) ∈ ω

theorem longRangeSetsLinked_mono {ω η : LongRangeConfiguration} (hωη : ω ⊆ η)
    {A B : Finset ℤ} (h : longRangeSetsLinked ω A B) :
    longRangeSetsLinked η A B := by
  rcases h with ⟨a, ha, b, hb, hab⟩
  exact ⟨a, ha, b, hb, hωη hab⟩

/-- A naturally ordered list of retained child clusters is joined by cross-bonds between every
consecutive pair. -/
def longRangeClusterChainLinked (ω : LongRangeConfiguration) :
    List (Finset ℤ) → Prop
  | [] => True
  | [_] => True
  | A :: B :: rest =>
      longRangeSetsLinked ω A B ∧ longRangeClusterChainLinked ω (B :: rest)

theorem longRangeClusterChainLinked_mono {ω η : LongRangeConfiguration}
    (hωη : ω ⊆ η) : ∀ {clusters : List (Finset ℤ)},
    longRangeClusterChainLinked ω clusters →
      longRangeClusterChainLinked η clusters
  | [], _ => trivial
  | [_], _ => trivial
  | A :: B :: rest, h =>
      ⟨longRangeSetsLinked_mono hωη h.1,
        longRangeClusterChainLinked_mono hωη h.2⟩

/-- Nonempty child clusters, in increasing child-index order. -/
noncomputable def longRangeRetainedChildren
    (cluster : ℕ → ℤ → LongRangeConfiguration → Finset ℤ)
    (arity k : ℕ) (z : ℤ) (ω : LongRangeConfiguration) : List (Finset ℤ) :=
  ((List.range arity).map fun i ↦ cluster k (z * arity + i) ω).filter (·.Nonempty)

/-- Union of a list of finite vertex sets. -/
def finsetListUnion {α : Type*} [DecidableEq α] : List (Finset α) → Finset α :=
  List.foldr (· ∪ ·) ∅

@[simp]
theorem finsetListUnion_nil {α : Type*} [DecidableEq α] :
    finsetListUnion ([] : List (Finset α)) = ∅ := rfl

@[simp]
theorem finsetListUnion_cons {α : Type*} [DecidableEq α]
    (s : Finset α) (l : List (Finset α)) :
    finsetListUnion (s :: l) = s ∪ finsetListUnion l := rfl

theorem mem_finsetListUnion_iff {α : Type*} [DecidableEq α]
    {x : α} {l : List (Finset α)} :
    x ∈ finsetListUnion l ↔ ∃ s ∈ l, x ∈ s := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

/-- Canonical retained cluster at each level.  The parameter `quota` is the minimum number of
retained children required at every nonzero level. -/
noncomputable def longRangeHierarchicalCluster (base arity quota : ℕ) :
    ℕ → ℤ → LongRangeConfiguration → Finset ℤ := fun k ↦ by
  classical
  exact Nat.rec
    (fun z ω ↦
      longRangeClassicalIf
        ((longRangeBlockNearestEdges base arity 0 z : Set (Sym2 ℤ)) ⊆ ω)
        (longRangeBlockVertices base arity 0 z)
        ∅)
    (fun k previous z ω ↦
      let children := longRangeRetainedChildren
        (fun _ ↦ previous) arity k z ω
      longRangeClassicalIf
        (quota ≤ children.length ∧ longRangeClusterChainLinked ω children)
        (finsetListUnion children)
        ∅)
    k

theorem longRangeHierarchicalCluster_zero (base arity quota : ℕ)
    (z : ℤ) (ω : LongRangeConfiguration) :
    longRangeHierarchicalCluster base arity quota 0 z ω =
      longRangeClassicalIf
        ((longRangeBlockNearestEdges base arity 0 z : Set (Sym2 ℤ)) ⊆ ω)
        (longRangeBlockVertices base arity 0 z)
        ∅ := by
  classical
  rfl

theorem longRangeHierarchicalCluster_succ (base arity quota k : ℕ)
    (z : ℤ) (ω : LongRangeConfiguration) :
    longRangeHierarchicalCluster base arity quota (k + 1) z ω =
      let children := longRangeRetainedChildren
        (fun _ ↦ longRangeHierarchicalCluster base arity quota k) arity k z ω
      longRangeClassicalIf
        (quota ≤ children.length ∧ longRangeClusterChainLinked ω children)
        (finsetListUnion children)
        ∅ := by
  classical
  rfl

/-- The finite event that the canonical level-`k` cluster is retained. -/
def longRangeBlockGoodEvent (base arity quota k : ℕ) (z : ℤ) :
    Set LongRangeConfiguration :=
  {ω | (longRangeHierarchicalCluster base arity quota k z ω).Nonempty}

/-! ### Source-facing existential good blocks -/

/-- Required connected-set size at level `k`. -/
def longRangeBlockTargetSize (base quota k : ℕ) : ℕ := base * quota ^ k

@[simp]
theorem longRangeBlockTargetSize_zero (base quota : ℕ) :
    longRangeBlockTargetSize base quota 0 = base := by
  simp [longRangeBlockTargetSize]

theorem longRangeBlockTargetSize_succ (base quota k : ℕ) :
    longRangeBlockTargetSize base quota (k + 1) =
      quota * longRangeBlockTargetSize base quota k := by
  rw [longRangeBlockTargetSize, longRangeBlockTargetSize, pow_succ]
  ac_rfl

theorem longRangeOpenGraph_mono {ω η : LongRangeConfiguration} (hωη : ω ⊆ η) :
    longRangeOpenGraph ω ≤ longRangeOpenGraph η := by
  intro x y hxy
  rw [longRangeOpenGraph_adj] at hxy ⊢
  exact ⟨hωη hxy.1, hxy.2⟩

/-- The open component of `x` inside a finite vertex block.  Its vertices retain the block
subtype, which makes the finite-cardinality and support arguments literal. -/
noncomputable def longRangeComponentInFinset (ω : LongRangeConfiguration)
    (B : Finset ℤ) (x : B) : Finset B := by
  classical
  exact B.attach.filter fun y ↦
    ((longRangeOpenGraph ω).induce (B : Set ℤ)).Reachable x y

theorem mem_longRangeComponentInFinset_iff
    {ω : LongRangeConfiguration} {B : Finset ℤ} {x y : B} :
    y ∈ longRangeComponentInFinset ω B x ↔
      ((longRangeOpenGraph ω).induce (B : Set ℤ)).Reachable x y := by
  classical
  simp [longRangeComponentInFinset]

theorem longRangeComponentInFinset_mono
    {ω η : LongRangeConfiguration} (hωη : ω ⊆ η)
    (B : Finset ℤ) (x : B) :
    longRangeComponentInFinset ω B x ⊆
      longRangeComponentInFinset η B x := by
  intro y hy
  rw [mem_longRangeComponentInFinset_iff] at hy ⊢
  apply hy.mono
  intro u v huv
  exact longRangeOpenGraph_mono hωη huv

theorem card_longRangeComponentInFinset_mono
    {ω η : LongRangeConfiguration} (hωη : ω ⊆ η)
    (B : Finset ℤ) (x : B) :
    (longRangeComponentInFinset ω B x).card ≤
      (longRangeComponentInFinset η B x).card :=
  Finset.card_le_card (longRangeComponentInFinset_mono hωη B x)

/-- Anchors whose internal open component has at least `m` vertices. -/
noncomputable def longRangeQualifyingAnchors (ω : LongRangeConfiguration)
    (B : Finset ℤ) (m : ℕ) : Finset B := by
  classical
  exact B.attach.filter fun x ↦ m ≤ (longRangeComponentInFinset ω B x).card

theorem mem_longRangeQualifyingAnchors_iff
    {ω : LongRangeConfiguration} {B : Finset ℤ} {m : ℕ} {x : B} :
    x ∈ longRangeQualifyingAnchors ω B m ↔
      m ≤ (longRangeComponentInFinset ω B x).card := by
  classical
  simp [longRangeQualifyingAnchors]

/-- Canonical large component in a finite block: choose the least anchor of a component of
size at least `m`, and return the empty set if no such anchor exists. -/
noncomputable def longRangeSelectedComponent (ω : LongRangeConfiguration)
    (B : Finset ℤ) (m : ℕ) : Finset B := by
  classical
  let Q := longRangeQualifyingAnchors ω B m
  exact if hQ : Q.Nonempty then longRangeComponentInFinset ω B (Q.min' hQ) else ∅

theorem card_longRangeSelectedComponent_ge_iff
    {ω : LongRangeConfiguration} {B : Finset ℤ} {m : ℕ} :
    m ≤ (longRangeSelectedComponent ω B m).card ↔
      m = 0 ∨ (longRangeQualifyingAnchors ω B m).Nonempty := by
  classical
  unfold longRangeSelectedComponent
  dsimp only
  split_ifs with hQ
  · have hminmem := Finset.min'_mem (longRangeQualifyingAnchors ω B m) hQ
    have hlarge := mem_longRangeQualifyingAnchors_iff.mp hminmem
    exact ⟨fun _ ↦ Or.inr hQ, fun _ ↦ hlarge⟩
  · simp [hQ]

theorem longRangeSelectedComponent_spec
    {ω : LongRangeConfiguration} {B : Finset ℤ} {m : ℕ}
    (h : ∃ x : B, m ≤ (longRangeComponentInFinset ω B x).card) :
    m ≤ (longRangeSelectedComponent ω B m).card := by
  rw [card_longRangeSelectedComponent_ge_iff]
  rcases h with ⟨x, hx⟩
  exact Or.inr ⟨x, mem_longRangeQualifyingAnchors_iff.mpr hx⟩

theorem exists_large_component_iff_selected
    {ω : LongRangeConfiguration} {B : Finset ℤ} {m : ℕ}
    (hB : B.Nonempty) :
    (∃ x : B, m ≤ (longRangeComponentInFinset ω B x).card) ↔
      m ≤ (longRangeSelectedComponent ω B m).card := by
  constructor
  · exact longRangeSelectedComponent_spec
  · intro h
    rw [card_longRangeSelectedComponent_ge_iff] at h
    rcases h with rfl | ⟨x, hx⟩
    · exact ⟨⟨hB.choose, hB.choose_spec⟩, Nat.zero_le _⟩
    · exact ⟨x, mem_longRangeQualifyingAnchors_iff.mp hx⟩

/-- A configuration is geometrically good on a block when that block contains an open connected
set of the recursively required size.  Unlike a largest-cluster selector, this existential event
is manifestly increasing and therefore is safe for renormalization. -/
def longRangeGeometricBlockGoodEvent (base arity quota k : ℕ) (z : ℤ) :
    Set LongRangeConfiguration :=
  {ω | ∃ x : longRangeBlockVertices base arity k z,
    longRangeBlockTargetSize base quota k ≤
      (longRangeComponentInFinset ω
        (longRangeBlockVertices base arity k z) x).card}

theorem isIncreasingEvent_longRangeGeometricBlockGoodEvent
    (base arity quota k : ℕ) (z : ℤ) :
    IsIncreasingEvent (longRangeGeometricBlockGoodEvent base arity quota k z) := by
  intro ω η hωη
  rintro ⟨x, hx⟩
  exact ⟨x, hx.trans (card_longRangeComponentInFinset_mono hωη _ x)⟩

/-- Opening all nearest-neighbour bonds in a positive-length base block connects the entire
block. -/
theorem connected_induce_longRangeBlockVertices_zero_of_nearest_open
    {base arity : ℕ} (hbase : 0 < base) (z : ℤ)
    {ω : LongRangeConfiguration}
    (hopen : (longRangeBlockNearestEdges base arity 0 z : Set (Sym2 ℤ)) ⊆ ω) :
    ((longRangeOpenGraph ω).induce
      (longRangeBlockVertices base arity 0 z : Set ℤ)).Connected := by
  let a : ℤ := z * base
  let f : SimpleGraph.pathGraph base →g
      (longRangeOpenGraph ω).induce
        (longRangeBlockVertices base arity 0 z : Set ℤ) :=
  { toFun := fun (i : Fin base) ↦ (⟨a + (i.val : ℤ), by
      change a + (i.val : ℤ) ∈ longRangeBlockVertices base arity 0 z
      rw [mem_longRangeBlockVertices_iff]
      simp only [longRangeBlockLength_zero]
      dsimp [a]
      constructor <;> omega⟩ :
        (longRangeBlockVertices base arity 0 z : Set ℤ))
    map_rel' := by
      intro i j hij
      rw [SimpleGraph.pathGraph_adj] at hij
      have hijne : i ≠ j := by
        intro h
        subst j
        omega
      change (longRangeOpenGraph ω).Adj (a + (i : ℤ)) (a + (j : ℤ))
      rw [longRangeOpenGraph_adj]
      constructor
      · rcases hij with hij | hij
        · have hi : a + (i : ℤ) ∈
              longRangeBlockVertices base arity 0 z := by
            rw [mem_longRangeBlockVertices_iff]
            simp only [longRangeBlockLength_zero]
            dsimp [a]
            constructor <;> omega
          have his : a + (i : ℤ) + 1 ∈
              longRangeBlockVertices base arity 0 z := by
            rw [mem_longRangeBlockVertices_iff]
            simp only [longRangeBlockLength_zero]
            dsimp [a]
            constructor <;> omega
          have he := hopen (mem_longRangeBlockNearestEdges_of_mem_succ hi his)
          simpa [show a + (j : ℤ) = a + (i : ℤ) + 1 by omega] using he
        · have hj : a + (j : ℤ) ∈
              longRangeBlockVertices base arity 0 z := by
            rw [mem_longRangeBlockVertices_iff]
            simp only [longRangeBlockLength_zero]
            dsimp [a]
            constructor <;> omega
          have hjs : a + (j : ℤ) + 1 ∈
              longRangeBlockVertices base arity 0 z := by
            rw [mem_longRangeBlockVertices_iff]
            simp only [longRangeBlockLength_zero]
            dsimp [a]
            constructor <;> omega
          have he := hopen (mem_longRangeBlockNearestEdges_of_mem_succ hj hjs)
          rw [show a + (i : ℤ) = a + (j : ℤ) + 1 by omega]
          simpa only [Sym2.eq_swap] using he
      · intro heq
        apply hijne
        apply Fin.ext
        exact_mod_cast (add_left_cancel heq) }
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    change x ∈ longRangeBlockVertices base arity 0 z at hx
    rw [mem_longRangeBlockVertices_iff] at hx
    simp only [longRangeBlockLength_zero] at hx
    have hnonneg : 0 ≤ x - a := by dsimp [a]; omega
    have hlt : (x - a).toNat < base := by
      rw [Int.toNat_lt hnonneg]
      dsimp [a]
      omega
    let i : Fin base := ⟨(x - a).toNat, hlt⟩
    refine ⟨i, Subtype.ext ?_⟩
    change a + ((x - a).toNat : ℤ) = x
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  have hbaseEq : base - 1 + 1 = base := by omega
  exact (hbaseEq ▸ SimpleGraph.pathGraph_connected (base - 1)).map f hf

/-- The all-nearest-open cylinder is a subset of the level-zero geometric good event. -/
theorem nearestOpen_subset_longRangeGeometricBlockGoodEvent
    {base arity quota : ℕ} (hbase : 0 < base) (z : ℤ) :
    {ω : LongRangeConfiguration |
        (longRangeBlockNearestEdges base arity 0 z : Set (Sym2 ℤ)) ⊆ ω} ⊆
      longRangeGeometricBlockGoodEvent base arity quota 0 z := by
  classical
  intro ω hω
  let B := longRangeBlockVertices base arity 0 z
  have hBnonempty : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have := congrArg Finset.card hEmpty
    simp [B, longRangeBlockVertices_card, longRangeBlockLength_zero, hbase.ne'] at this
  let x : B := ⟨hBnonempty.choose, hBnonempty.choose_spec⟩
  refine ⟨x, ?_⟩
  have hconn := connected_induce_longRangeBlockVertices_zero_of_nearest_open hbase z hω
  have hcomp : longRangeComponentInFinset ω B x = B.attach := by
    unfold longRangeComponentInFinset
    apply Finset.filter_eq_self.mpr
    intro y _hy
    exact hconn.preconnected x y
  rw [hcomp, Finset.card_attach, longRangeBlockTargetSize_zero]
  dsimp [B]
  rw [longRangeBlockVertices_card, longRangeBlockLength_zero]

/-! ### Finite supports -/

/-- All unordered pairs whose endpoints lie in a block.  This intentionally includes diagonal
pairs; their density is zero and retaining them makes support proofs algebraically simpler. -/
noncomputable def longRangeBlockEdgeSupport (base arity k : ℕ) (z : ℤ) :
    Finset (Sym2 ℤ) :=
  ((longRangeBlockVertices base arity k z) ×ˢ
    longRangeBlockVertices base arity k z).image fun xy ↦ s(xy.1, xy.2)

theorem sym2_mem_longRangeBlockEdgeSupport
    {base arity k : ℕ} {z x y : ℤ}
    (hx : x ∈ longRangeBlockVertices base arity k z)
    (hy : y ∈ longRangeBlockVertices base arity k z) :
    s(x, y) ∈ longRangeBlockEdgeSupport base arity k z := by
  classical
  rw [longRangeBlockEdgeSupport, Finset.mem_image]
  exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

theorem dependsOn_longRangeGeometricBlockGoodEvent
    (base arity quota k : ℕ) (z : ℤ) :
    DependsOn (longRangeBlockEdgeSupport base arity k z)
      (longRangeGeometricBlockGoodEvent base arity quota k z) := by
  classical
  intro ω η htrace
  let B := longRangeBlockVertices base arity k z
  have hgraph :
      (longRangeOpenGraph ω).induce (B : Set ℤ) =
        (longRangeOpenGraph η).induce (B : Set ℤ) := by
    ext x y
    change (longRangeOpenGraph ω).Adj x.val y.val ↔
      (longRangeOpenGraph η).Adj x.val y.val
    rw [longRangeOpenGraph_adj, longRangeOpenGraph_adj]
    apply and_congr
    · exact htrace s(x.val, y.val)
        (sym2_mem_longRangeBlockEdgeSupport x.property y.property)
    · rfl
  change (∃ x : B, longRangeBlockTargetSize base quota k ≤
      (longRangeComponentInFinset ω B x).card) ↔
    ∃ x : B, longRangeBlockTargetSize base quota k ≤
      (longRangeComponentInFinset η B x).card
  have hcomp (x : B) :
      longRangeComponentInFinset ω B x =
        longRangeComponentInFinset η B x := by
    ext y
    rw [mem_longRangeComponentInFinset_iff,
      mem_longRangeComponentInFinset_iff]
    simpa only [hgraph]
  simp_rw [hcomp]

/-- The canonical selected component is a function of the internal block coordinates only. -/
theorem dependsOnFun_longRangeSelectedComponent
    (base arity k : ℕ) (z : ℤ) (m : ℕ) :
    DependsOnFun (longRangeBlockEdgeSupport base arity k z)
      (fun ω ↦ longRangeSelectedComponent ω
        (longRangeBlockVertices base arity k z) m) := by
  classical
  intro ω η htrace
  let B := longRangeBlockVertices base arity k z
  have hgraph :
      (longRangeOpenGraph ω).induce (B : Set ℤ) =
        (longRangeOpenGraph η).induce (B : Set ℤ) := by
    ext x y
    change (longRangeOpenGraph ω).Adj x.val y.val ↔
      (longRangeOpenGraph η).Adj x.val y.val
    rw [longRangeOpenGraph_adj, longRangeOpenGraph_adj]
    apply and_congr
    · exact htrace s(x.val, y.val)
        (sym2_mem_longRangeBlockEdgeSupport x.property y.property)
    · rfl
  have hcomp (x : B) :
      longRangeComponentInFinset ω B x =
        longRangeComponentInFinset η B x := by
    ext y
    rw [mem_longRangeComponentInFinset_iff,
      mem_longRangeComponentInFinset_iff]
    simpa only [hgraph]
  have hqual : longRangeQualifyingAnchors ω B m =
      longRangeQualifyingAnchors η B m := by
    ext x
    rw [mem_longRangeQualifyingAnchors_iff,
      mem_longRangeQualifyingAnchors_iff, hcomp]
  unfold longRangeSelectedComponent
  dsimp only
  rw [← hqual]
  split_ifs with hQ
  · exact hcomp _
  · rfl

theorem measurableSet_longRangeGeometricBlockGoodEvent
    (base arity quota k : ℕ) (z : ℤ) :
    MeasurableSet (longRangeGeometricBlockGoodEvent base arity quota k z) :=
  (dependsOn_longRangeGeometricBlockGoodEvent base arity quota k z).measurableSet

end Percolation
