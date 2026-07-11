import Percolation.Critical.TreeGraph

/-!
# Canonical labelled trivalent skeletons

This module gives a recursive decoder for the skeletons in Grimmett (6.92)--(6.96).  A skeleton
with three labelled leaves is the tripod.  A skeleton with `k+1` leaves is obtained uniquely by
inserting leaf `k` into one of the `2k-3` edges of a `k`-leaf skeleton.
-/

namespace Percolation

open Set SimpleGraph
open scoped BigOperators ENNReal unitInterval

/-- Recursive insertion codes for labelled trivalent skeletons.  This concrete decoder carries
the vertex and edge geometry used by the realization theorem below.  The extensionally equal
counting code in `TreeGraph.lean` is deliberately separate, so enumeration does not erase these
geometric fields. -/
@[reducible] def CubicConnectivitySkeleton : ℕ → Type
  | 0 | 1 | 2 => Empty
  | 3 => PUnit
  | n + 4 => CubicConnectivitySkeleton (n + 3) × Fin (2 * (n + 3) - 3)

@[reducible] private def cubicConnectivitySkeletonFintype :
    (n : ℕ) → Fintype (CubicConnectivitySkeleton n)
  | 0 | 1 | 2 => inferInstance
  | 3 => inferInstance
  | n + 4 =>
      letI := cubicConnectivitySkeletonFintype (n + 3)
      inferInstance

@[reducible] private def cubicConnectivitySkeletonDecidableEq :
    (n : ℕ) → DecidableEq (CubicConnectivitySkeleton n)
  | 0 | 1 | 2 => fun x ↦ nomatch x
  | 3 => inferInstance
  | n + 4 =>
      letI := cubicConnectivitySkeletonDecidableEq (n + 3)
      inferInstance

attribute [local instance] cubicConnectivitySkeletonFintype
attribute [local instance] cubicConnectivitySkeletonDecidableEq

/-- Vertices of a decoded skeleton.  An insertion adds one trivalent vertex and one leaf. -/
@[reducible] def CubicConnectivitySkeleton.Vertex :
    {n : ℕ} → CubicConnectivitySkeleton n → Type
  | 0, s | 1, s | 2, s => nomatch s
  | 3, _ => Fin 4
  | _n + 4, s => CubicConnectivitySkeleton.Vertex s.1 ⊕ Fin 2

@[reducible] private def cubicConnectivitySkeletonVertexFintype :
    {n : ℕ} → (s : CubicConnectivitySkeleton n) → Fintype s.Vertex
  | 0, s | 1, s | 2, s => nomatch s
  | 3, _ => inferInstance
  | _n + 4, s =>
      letI := cubicConnectivitySkeletonVertexFintype s.1
      inferInstance

@[reducible] private def cubicConnectivitySkeletonVertexDecidableEq :
    {n : ℕ} → (s : CubicConnectivitySkeleton n) → DecidableEq s.Vertex
  | 0, s | 1, s | 2, s => nomatch s
  | 3, _ => inferInstance
  | _n + 4, s =>
      letI := cubicConnectivitySkeletonVertexDecidableEq s.1
      inferInstance

attribute [local instance] cubicConnectivitySkeletonVertexFintype
attribute [local instance] cubicConnectivitySkeletonVertexDecidableEq

/-- The vertex carrying a given exterior label. -/
@[reducible] def CubicConnectivitySkeleton.leaf :
    {n : ℕ} → (s : CubicConnectivitySkeleton n) → Fin n → s.Vertex
  | 0, s, _ => nomatch s
  | 1, s, _ => nomatch s
  | 2, s, _ => nomatch s
  | 3, _, i => ⟨i, by omega⟩
  | n + 4, s, i =>
      if h : i.1 < n + 3 then
        Sum.inl (s.1.leaf ⟨i.1, h⟩)
      else Sum.inr ⟨1, by omega⟩

/-- Number of edges in a labelled skeleton with `n` leaves. -/
@[reducible] def CubicConnectivitySkeleton.edgeCount (n : ℕ) : ℕ := 2 * n - 3

/-- Ordered endpoints of the decoded edges.  The order is only an implementation device; all
connectivity weights are symmetric. -/
@[reducible] def CubicConnectivitySkeleton.edge :
    {n : ℕ} → (s : CubicConnectivitySkeleton n) →
      Fin (CubicConnectivitySkeleton.edgeCount n) → s.Vertex × s.Vertex
  | 0, s, _ => nomatch s
  | 1, s, _ => nomatch s
  | 2, s, _ => nomatch s
  | 3, _, i => (⟨3, by omega⟩, ⟨i.1, by
      have hi : i.1 < 3 := by
        simpa [CubicConnectivitySkeleton.edgeCount] using i.2
      exact hi.trans (by omega)⟩)
  | n + 4, s, i =>
      let old := s.1
      let chosen := s.2
      let E := CubicConnectivitySkeleton.edgeCount (n + 3)
      let newInterior : s.Vertex := Sum.inr ⟨0, by omega⟩
      let newLeaf : s.Vertex := Sum.inr ⟨1, by omega⟩
      if hi : i.1 < E then
        let j : Fin E := ⟨i.1, hi⟩
        let ab := old.edge j
        if hj : j = chosen then
          (Sum.inl ab.1, newInterior)
        else
          (Sum.inl ab.1, Sum.inl ab.2)
      else if hiE : i.1 = E then
        let ab := old.edge chosen
        (newInterior, Sum.inl ab.2)
      else
        (newInterior, newLeaf)

/-- The distinguished edge whose second endpoint is exterior vertex `0`. -/
def CubicConnectivitySkeleton.rootEdge :
    {n : ℕ} → (s : CubicConnectivitySkeleton n) →
      Fin (CubicConnectivitySkeleton.edgeCount n)
  | 0, s | 1, s | 2, s => nomatch s
  | 3, _ => ⟨0, by simp [CubicConnectivitySkeleton.edgeCount]⟩
  | n + 4, s =>
      let E := CubicConnectivitySkeleton.edgeCount (n + 3)
      if h : s.1.rootEdge = s.2 then
        ⟨E, by dsimp [E, CubicConnectivitySkeleton.edgeCount]; omega⟩
      else
        ⟨s.1.rootEdge.1, by
          have hlt := s.1.rootEdge.2
          simp [CubicConnectivitySkeleton.edgeCount] at hlt ⊢
          omega⟩

/-- The distinguished root edge really ends at leaf `0`. -/
theorem CubicConnectivitySkeleton.edge_rootEdge_snd_eq_leaf_zero
    {n : ℕ} (s : CubicConnectivitySkeleton n) (hn : 3 ≤ n) :
    (s.edge s.rootEdge).2 = s.leaf ⟨0, by omega⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | _ | _ | n)
      · omega
      · omega
      · omega
      · rfl
      · have hold := ih (n + 3) (by omega) s.1 (by omega)
        simp only [CubicConnectivitySkeleton.rootEdge]
        split_ifs with hroot
        · have hsel : (s.1.edge s.2).2 = s.1.leaf ⟨0, by omega⟩ := by
            simpa [hroot] using hold
          simp [CubicConnectivitySkeleton.edge, CubicConnectivitySkeleton.leaf,
            CubicConnectivitySkeleton.edgeCount, hroot, hsel]
        · simp [CubicConnectivitySkeleton.edge, CubicConnectivitySkeleton.leaf,
            CubicConnectivitySkeleton.edgeCount, hroot, hold]

@[simp] theorem cubicConnectivitySkeleton_card_three :
    Fintype.card (CubicConnectivitySkeleton 3) = 1 := by decide

/-- The recursive code has exactly the source skeleton count. -/
theorem cubicConnectivitySkeleton_card_eq (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (CubicConnectivitySkeleton n) = connectivitySkeletonCount n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | _ | _ | n)
      · omega
      · omega
      · omega
      · simp [CubicConnectivitySkeleton, connectivitySkeletonCount]
      · change Fintype.card
            (CubicConnectivitySkeleton (n + 3) × Fin (2 * (n + 3) - 3)) = _
        simp only [Fintype.card_prod, Fintype.card_fin]
        rw [ih (n + 3) (by omega) (by omega),
          connectivitySkeletonCount_succ (n := n + 3) (by omega), mul_comm]

/-- Instance-independent form of `cubicConnectivitySkeleton_card_eq`. -/
theorem cubicConnectivitySkeleton_natCard_eq (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (CubicConnectivitySkeleton n) = connectivitySkeletonCount n := by
  rw [Nat.card_eq_fintype_card]
  exact cubicConnectivitySkeleton_card_eq n hn

/-! ### Realizations by edge-disjoint walks -/

/-- A realization assigns lattice vertices to a skeleton and an edge-disjoint walk to every
decoded edge. -/
structure CubicConnectivitySkeleton.Realization {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (s : CubicConnectivitySkeleton n) (ψ : s.Vertex → V) where
  walk : ∀ e : Fin (CubicConnectivitySkeleton.edgeCount n),
    G.Walk (ψ (s.edge e).1) (ψ (s.edge e).2)
  edgeDisjoint : ∀ i j, i ≠ j → (walk i).edges.Disjoint (walk j).edges

/-- First hit of a finite family of walks.  The initial segment is edge-disjoint from every old
walk, and its endpoint lies on the selected old walk. -/
private theorem exists_firstHit_walkFamily
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    {G : SimpleGraph V} {c z : V}
    {a b : ι → V} (w : ∀ i, G.Walk (a i) (b i)) (q : G.Walk c z)
    (hz : ∃ i, z ∈ (w i).support) :
    ∃ e : ι, ∃ u : V, ∃ hu : u ∈ (w e).support, ∃ r : G.Walk c u,
      ∀ i, r.edges.Disjoint (w i).edges := by
  classical
  have hex : ∃ j : ℕ, j ≤ q.length ∧ ∃ i, q.getVert j ∈ (w i).support := by
    obtain ⟨i, hi⟩ := hz
    exact ⟨q.length, le_rfl, i, by simpa using hi⟩
  let j := Nat.find hex
  obtain ⟨hjlen, e, hje⟩ := Nat.find_spec hex
  let u := q.getVert j
  let r : G.Walk c u := q.take j
  refine ⟨e, u, hje, r, ?_⟩
  intro t
  rw [List.disjoint_left]
  intro edge hre hte
  induction edge using Sym2.inductionOn with
  | _ x y =>
    have hxy : x ≠ y := (r.adj_of_mem_edges hre).ne
    let v : V := if x = u then y else x
    have hvu : v ≠ u := by
      dsimp [v]
      split_ifs with hxu
      · intro hyu
        exact hxy (hxu.trans hyu.symm)
      · exact hxu
    have hvR : v ∈ r.support := by
      dsimp [v]
      split_ifs
      · exact r.snd_mem_support_of_mem_edges hre
      · exact r.fst_mem_support_of_mem_edges hre
    have hvT : v ∈ (w t).support := by
      dsimp [v]
      split_ifs
      · exact (w t).snd_mem_support_of_mem_edges hte
      · exact (w t).fst_mem_support_of_mem_edges hte
    obtain ⟨i, hiEq, hiLen⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvR
    have hrlen : r.length = j := by
      dsimp [r]
      rw [q.take_length, min_eq_left hjlen]
    have hijle : i ≤ j := by simpa [hrlen] using hiLen
    have hqi : q.getVert i = v := by
      simpa [r, q.take_getVert, min_eq_right hijle] using hiEq
    have hij : i < j := by
      apply lt_of_le_of_ne hijle
      intro hijEq
      apply hvu
      rw [← hiEq, hijEq]
      simp [r, u, q.take_getVert]
    have hcand : i ≤ q.length ∧ ∃ t, q.getVert i ∈ (w t).support :=
      ⟨hijle.trans hjlen, t, hqi.symm ▸ hvT⟩
    exact (not_lt_of_ge (Nat.find_min' hex hcand)) hij

private theorem List.Disjoint.monoSublist {α : Type*} {a b a' b' : List α}
    (h : a.Disjoint b) (ha : a' ⊆ a) (hb : b' ⊆ b) : a'.Disjoint b' := by
  rw [List.disjoint_left] at h ⊢
  exact fun _ hxa hxb ↦ h (ha hxa) (hb hxb)

/-- Base case of the skeleton construction: the three-terminal tripod. -/
theorem exists_skeletonRealization_three
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (x : Fin 3 → V)
    (h₁ : G.Reachable (x 0) (x 1)) (h₂ : G.Reachable (x 0) (x 2)) :
    ∃ s : CubicConnectivitySkeleton 3, ∃ ψ : s.Vertex → V,
      (∀ i, ψ (s.leaf i) = x i) ∧ Nonempty (s.Realization G ψ) := by
  obtain ⟨u, w₀, w₁, w₂, h01, h02, h12⟩ :=
    exists_three_pairwise_edgeDisjoint_walks_of_reachable G h₁ h₂
  let s : CubicConnectivitySkeleton 3 := PUnit.unit
  let ψ : s.Vertex → V := ![x 0, x 1, x 2, u]
  let walk : ∀ e : Fin (CubicConnectivitySkeleton.edgeCount 3),
      G.Walk (ψ (s.edge e).1) (ψ (s.edge e).2) := by
    intro e
    refine Fin.cases ?_ (fun e₂ ↦ ?_) e
    · simpa [s, ψ] using w₀
    · refine Fin.cases ?_ (fun e₁ ↦ ?_) e₂
      · simpa [s, ψ] using w₁
      · refine Fin.cases ?_ (fun e₀ ↦ Fin.elim0 e₀) e₁
        simpa [s, ψ] using w₂
  have hwalk₀ : (walk 0).edges = w₀.edges := by rfl
  have hwalk₁ : (walk 1).edges = w₁.edges := by rfl
  have hwalk₂ : (walk 2).edges = w₂.edges := by rfl
  refine ⟨s, ψ, ?_, ⟨⟨walk, ?_⟩⟩⟩
  · intro i
    fin_cases i <;> rfl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [hwalk₀, hwalk₁] using h01
    · simpa only [hwalk₀, hwalk₂] using h02
    · simpa only [hwalk₀, hwalk₁] using h01.symm
    · exact (hij rfl).elim
    · simpa only [hwalk₁, hwalk₂] using h12
    · simpa only [hwalk₀, hwalk₂] using h02.symm
    · simpa only [hwalk₁, hwalk₂] using h12.symm
    · exact (hij rfl).elim

/-- Insert a new labelled leaf into a realized skeleton.  The path from the new terminal is
stopped at its first hit of the old realization; consequently its initial segment is disjoint
from every old skeleton edge. -/
private theorem CubicConnectivitySkeleton.Realization.exists_insert
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {n : ℕ} (hn : 3 ≤ n)
    {s : CubicConnectivitySkeleton n} {ψ : s.Vertex → V}
    (R : s.Realization G ψ) (z : V)
    (hz : G.Reachable z (ψ (s.leaf ⟨0, by omega⟩))) :
    ∃ s' : CubicConnectivitySkeleton (n + 1), ∃ ψ' : s'.Vertex → V,
      (∀ i : Fin n, ψ' (s'.leaf i.castSucc) = ψ (s.leaf i)) ∧
      ψ' (s'.leaf (Fin.last n)) = z ∧ Nonempty (s'.Realization G ψ') := by
  classical
  obtain ⟨q⟩ := hz
  let oldWalk : ∀ i, G.Walk (ψ (s.edge i).1) (ψ (s.edge i).2) :=
    fun i ↦ (R.walk i).toPath
  have oldWalk_isTrail : ∀ i, (oldWalk i).IsTrail := by
    intro i
    exact (R.walk i).toPath.isTrail
  have oldWalk_disjoint : ∀ i j, i ≠ j → (oldWalk i).edges.Disjoint (oldWalk j).edges := by
    intro i j hij
    exact List.Disjoint.monoSublist (R.edgeDisjoint i j hij)
      (R.walk i).edges_toPath_subset (R.walk j).edges_toPath_subset
  have hzOld : ∃ i, ψ (s.leaf ⟨0, by omega⟩) ∈ (oldWalk i).support := by
    refine ⟨s.rootEdge, ?_⟩
    rw [← s.edge_rootEdge_snd_eq_leaf_zero hn]
    exact (oldWalk s.rootEdge).end_mem_support
  let qPath : G.Walk z (ψ (s.leaf ⟨0, by omega⟩)) := q.toPath
  obtain ⟨e, u, hu, r, hr⟩ :=
    exists_firstHit_walkFamily oldWalk qPath hzOld
  let E := CubicConnectivitySkeleton.edgeCount n
  have hnform : ∃ k, n = k + 3 := by exact ⟨n - 3, by omega⟩
  obtain ⟨k, rfl⟩ := hnform
  let s' : CubicConnectivitySkeleton (k + 3 + 1) := (s, e)
  let ψ' : s'.Vertex → V
    | Sum.inl v => ψ v
    | Sum.inr i => if i.1 = 0 then u else z
  let walk : ∀ i : Fin (CubicConnectivitySkeleton.edgeCount (k + 3 + 1)),
      G.Walk (ψ' (s'.edge i).1) (ψ' (s'.edge i).2) := by
    intro i
    if hi : i.1 < E then
      let j : Fin E := ⟨i.1, hi⟩
      if hje : j = e then
        exact ((oldWalk e).takeUntil u hu).copy
          (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, j, hje])
          (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, j, hje])
      else
        exact (oldWalk j).copy
          (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, j, hje])
          (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, j, hje])
    else if hiE : i.1 = E then
      exact ((oldWalk e).dropUntil u hu).copy
        (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, hiE])
        (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, hiE])
    else
      exact r.reverse.copy
        (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, hiE])
        (by simp [s', ψ', CubicConnectivitySkeleton.edge, E, hi, hiE])
  have walk_edges_lt_eq (i : Fin (CubicConnectivitySkeleton.edgeCount (k + 3 + 1)))
      (hi : i.1 < E) (hie : (⟨i.1, hi⟩ : Fin E) = e) :
      (walk i).edges = ((oldWalk e).takeUntil u hu).edges := by
    simp [walk, hi, hie]
  have walk_edges_lt_ne (i : Fin (CubicConnectivitySkeleton.edgeCount (k + 3 + 1)))
      (hi : i.1 < E) (hie : (⟨i.1, hi⟩ : Fin E) ≠ e) :
      (walk i).edges = (oldWalk ⟨i.1, hi⟩).edges := by
    simp [walk, hi, hie]
  have walk_edges_mid (i : Fin (CubicConnectivitySkeleton.edgeCount (k + 3 + 1)))
      (hi : ¬i.1 < E) (hiE : i.1 = E) :
      (walk i).edges = ((oldWalk e).dropUntil u hu).edges := by
    simp [walk, hi, hiE]
  have walk_edges_last (i : Fin (CubicConnectivitySkeleton.edgeCount (k + 3 + 1)))
      (hi : ¬i.1 < E) (hiE : i.1 ≠ E) :
      (walk i).edges = r.reverse.edges := by
    simp [walk, hi, hiE]
  refine ⟨s', ψ', ?_, ?_, ⟨⟨walk, ?_⟩⟩⟩
  · intro i
    simp [s', ψ', CubicConnectivitySkeleton.leaf, i.2]
  · simp [s', ψ', CubicConnectivitySkeleton.leaf]
  · intro i j hij
    by_cases hi : i.1 < E
    · let ii : Fin E := ⟨i.1, hi⟩
      by_cases hie : ii = e
      · by_cases hj : j.1 < E
        · let jj : Fin E := ⟨j.1, hj⟩
          by_cases hje : jj = e
          · exfalso
            apply hij
            have hiij : ii = jj := hie.trans hje.symm
            exact Fin.ext (by simpa [ii, jj] using congrArg Fin.val hiij)
          · have hd := List.Disjoint.monoSublist (oldWalk_disjoint e jj (Ne.symm hje))
                ((oldWalk e).edges_takeUntil_subset hu) (fun _ h ↦ h)
            rw [walk_edges_lt_eq i hi (by simpa [ii] using hie),
              walk_edges_lt_ne j hj (by simpa [jj] using hje)]
            exact hd
        · by_cases hjE : j.1 = E
          · have hd := (oldWalk_isTrail e).disjoint_edges_takeUntil_dropUntil hu
            rw [walk_edges_lt_eq i hi (by simpa [ii] using hie), walk_edges_mid j hj hjE]
            exact hd
          · have hd := List.Disjoint.monoSublist (hr e).symm
                ((oldWalk e).edges_takeUntil_subset hu) (fun _ h ↦ h)
            rw [walk_edges_lt_eq i hi (by simpa [ii] using hie), walk_edges_last j hj hjE,
              SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_right]
            exact hd
      · by_cases hj : j.1 < E
        · let jj : Fin E := ⟨j.1, hj⟩
          by_cases hje : jj = e
          · have hd := List.Disjoint.monoSublist (oldWalk_disjoint ii e hie)
                (fun _ h ↦ h) ((oldWalk e).edges_takeUntil_subset hu)
            rw [walk_edges_lt_ne i hi (by simpa [ii] using hie),
              walk_edges_lt_eq j hj (by simpa [jj] using hje)]
            exact hd
          · have hiij : ii ≠ jj := by
              intro hEq
              apply hij
              have hv : i.1 = j.1 := by
                simpa [ii, jj] using congrArg Fin.val hEq
              exact Fin.ext hv
            rw [walk_edges_lt_ne i hi (by simpa [ii] using hie),
              walk_edges_lt_ne j hj (by simpa [jj] using hje)]
            exact oldWalk_disjoint ii jj hiij
        · by_cases hjE : j.1 = E
          · have hd := List.Disjoint.monoSublist (oldWalk_disjoint ii e hie)
                (fun _ h ↦ h) ((oldWalk e).edges_dropUntil_subset hu)
            rw [walk_edges_lt_ne i hi (by simpa [ii] using hie), walk_edges_mid j hj hjE]
            exact hd
          · have hd := (hr ii).symm
            rw [walk_edges_lt_ne i hi (by simpa [ii] using hie), walk_edges_last j hj hjE,
              SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_right]
            exact hd
    · by_cases hiE : i.1 = E
      · by_cases hj : j.1 < E
        · let jj : Fin E := ⟨j.1, hj⟩
          by_cases hje : jj = e
          · have hd :=
                ((oldWalk_isTrail e).disjoint_edges_takeUntil_dropUntil hu).symm
            rw [walk_edges_mid i hi hiE,
              walk_edges_lt_eq j hj (by simpa [jj] using hje)]
            exact hd
          · have hd := List.Disjoint.monoSublist (oldWalk_disjoint e jj (Ne.symm hje))
                ((oldWalk e).edges_dropUntil_subset hu) (fun _ h ↦ h)
            rw [walk_edges_mid i hi hiE,
              walk_edges_lt_ne j hj (by simpa [jj] using hje)]
            exact hd
        · by_cases hjE : j.1 = E
          · exact (hij (Fin.ext (hiE.trans hjE.symm))).elim
          · have hd := List.Disjoint.monoSublist (hr e).symm
                ((oldWalk e).edges_dropUntil_subset hu) (fun _ h ↦ h)
            rw [walk_edges_mid i hi hiE, walk_edges_last j hj hjE,
              SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_right]
            exact hd
      · by_cases hj : j.1 < E
        · let jj : Fin E := ⟨j.1, hj⟩
          by_cases hje : jj = e
          · have hd := List.Disjoint.monoSublist (hr e)
                (fun _ h ↦ h) ((oldWalk e).edges_takeUntil_subset hu)
            rw [walk_edges_last i hi hiE,
              walk_edges_lt_eq j hj (by simpa [jj] using hje),
              SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_left]
            exact hd
          · have hd := hr jj
            rw [walk_edges_last i hi hiE,
              walk_edges_lt_ne j hj (by simpa [jj] using hje),
              SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_left]
            exact hd
        · by_cases hjE : j.1 = E
          · have hd := List.Disjoint.monoSublist (hr e)
                (fun _ h ↦ h) ((oldWalk e).edges_dropUntil_subset hu)
            rw [walk_edges_last i hi hiE, walk_edges_mid j hj hjE,
              SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_left]
            exact hd
          · have hiLast : i.1 = E + 1 := by
              have hCount : CubicConnectivitySkeleton.edgeCount (k + 3 + 1) = E + 2 := by
                simp [CubicConnectivitySkeleton.edgeCount, E]
                omega
              have hiBound : i.1 < E + 2 := by simpa only [hCount] using i.2
              omega
            have hjLast : j.1 = E + 1 := by
              have hCount : CubicConnectivitySkeleton.edgeCount (k + 3 + 1) = E + 2 := by
                simp [CubicConnectivitySkeleton.edgeCount, E]
                omega
              have hjBound : j.1 < E + 2 := by simpa only [hCount] using j.2
              omega
            exact (hij (Fin.ext (hiLast.trans hjLast.symm))).elim

/-- Every finite connected family of at least three labelled terminals admits a realization by
one of the canonical trivalent skeletons. -/
theorem exists_skeletonRealization
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (n : ℕ) (x : Fin (n + 3) → V)
    (h : ∀ i, G.Reachable (x 0) (x i)) :
    ∃ s : CubicConnectivitySkeleton (n + 3), ∃ ψ : s.Vertex → V,
      (∀ i, ψ (s.leaf i) = x i) ∧ Nonempty (s.Realization G ψ) := by
  induction n with
  | zero =>
      exact exists_skeletonRealization_three G x (h 1) (h 2)
  | succ n ih =>
      let xOld : Fin (n + 3) → V := fun i => x i.castSucc
      obtain ⟨s, ψ, hleaf, R⟩ := ih xOld (fun i ↦ h i.castSucc)
      let z := x (Fin.last (n + 3))
      have hz : G.Reachable z (ψ (s.leaf ⟨0, by omega⟩)) := by
        rw [hleaf]
        exact (h (Fin.last (n + 3))).symm.trans (h 0)
      obtain ⟨s', ψ', hold, hnew, R'⟩ :=
        R.some.exists_insert (by omega) z hz
      refine ⟨s', ψ', ?_, R'⟩
      intro i
      by_cases hi : i.1 < n + 3
      · let j : Fin (n + 3) := ⟨i.1, hi⟩
        simpa [j, xOld] using (hold j).trans (hleaf j)
      · have hiLast : i = Fin.last (n + 3) := Fin.ext (by
          change i.1 = n + 3
          omega)
        simpa [hiLast, z] using hnew

/-! ### The tree-graph event and inequality (6.93) -/

/-- The event that all labelled terminals are joined to terminal `0`. -/
def orderedMultiPointConnectionEvent (d n : ℕ) (x : Fin (n + 3) → Cubic d) :
    Set (EdgeConfiguration d) :=
  {ω | ∀ i, ω ∈ connectionEvent d (x 0) (x i)}

/-- Pairwise edge-disjoint open connections along every decoded edge of a skeleton. -/
def skeletonDisjointConnectionEvent {d n : ℕ} (s : CubicConnectivitySkeleton n)
    (ψ : s.Vertex → Cubic d) : Set (EdgeConfiguration d) :=
  ExistsPairwiseDisjointOpenWalks d
    (Finset.univ : Finset (Fin (CubicConnectivitySkeleton.edgeCount n)))
    (fun e ↦ ψ (s.edge e).1) (fun e ↦ ψ (s.edge e).2)

/-- A prescribed realization contributes only when its exterior labels are the supplied
terminals. -/
def labelledSkeletonEvent {d n : ℕ} (s : CubicConnectivitySkeleton (n + 3))
    (ψ : s.Vertex → Cubic d) (x : Fin (n + 3) → Cubic d) :
    Set (EdgeConfiguration d) :=
  if ∀ i, ψ (s.leaf i) = x i then skeletonDisjointConnectionEvent s ψ else ∅

private theorem disjoint_walkEdgeFinset_of_map_edges_disjoint
    {d : ℕ} {ω : EdgeConfiguration d} {a b c e : Cubic d}
    {p : (cubicOpenGraph d ω).Walk a b} {q : (cubicOpenGraph d ω).Walk c e}
    (h : p.edges.Disjoint q.edges) :
    Disjoint (walkEdgeFinset (p.map (cubicOpenGraphHom d ω)))
      (walkEdgeFinset (q.map (cubicOpenGraphHom d ω))) := by
  rw [Finset.disjoint_left]
  intro edge hp hq
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_map] at hp hq
  rw [List.disjoint_left] at h
  obtain ⟨ep, hep, hepMap⟩ := List.mem_map.mp hp
  obtain ⟨eq, heq, heqMap⟩ := List.mem_map.mp hq
  have hinj : Function.Injective (Sym2.map (cubicOpenGraphHom d ω)) :=
    Sym2.map.injective fun _ _ hxy ↦ hxy
  have hepeq : ep = eq := hinj (hepMap.trans heqMap.symm)
  exact h hep (hepeq ▸ heq)

/-- Deterministic tree extraction: a common open cluster contains a labelled skeleton whose
edge paths are pairwise edge-disjoint. -/
theorem orderedMultiPointConnectionEvent_subset_iUnion_skeleton
    (d n : ℕ) (x : Fin (n + 3) → Cubic d) :
    orderedMultiPointConnectionEvent d n x ⊆
      ⋃ s : CubicConnectivitySkeleton (n + 3),
        ⋃ ψ : s.Vertex → Cubic d, labelledSkeletonEvent s ψ x := by
  classical
  intro ω hω
  let Gω := cubicOpenGraph d ω
  have hreach : ∀ i, Gω.Reachable (x 0) (x i) := by
    intro i
    obtain ⟨w, hw⟩ := hω i
    exact (nonempty_cubicOpenGraph_walk_of_walkIsOpen w hw).some.reachable
  obtain ⟨s, ψ, hleaf, R⟩ := exists_skeletonRealization Gω n x hreach
  rw [Set.mem_iUnion]
  refine ⟨s, ?_⟩
  rw [Set.mem_iUnion]
  let φ : s.Vertex → Cubic d := fun v ↦ (ψ v : Cubic d)
  refine ⟨φ, ?_⟩
  have hφ : ∀ i, φ (s.leaf i) = x i := by simpa [φ] using hleaf
  rw [labelledSkeletonEvent, if_pos hφ]
  let w : ∀ e : Fin (CubicConnectivitySkeleton.edgeCount (n + 3)),
      (cubicGraph d).Walk (φ (s.edge e).1) (φ (s.edge e).2) :=
    fun e ↦ (R.some.walk e).map (cubicOpenGraphHom d ω)
  refine ⟨w, ?_, ?_⟩
  · intro e _he
    exact walkIsOpen_map_cubicOpenGraphHom (R.some.walk e)
  · intro i _hi j _hj hij
    exact disjoint_walkEdgeFinset_of_map_edges_disjoint
      (R.some.edgeDisjoint i j hij)

/-- The product weight assigned to one labelled placement of one connectivity skeleton. -/
noncomputable def skeletonConnectivityWeight {d n : ℕ}
    (p : unitInterval) (s : CubicConnectivitySkeleton (n + 3))
    (ψ : s.Vertex → Cubic d) (x : Fin (n + 3) → Cubic d) : ℝ≥0∞ :=
  if ∀ i, ψ (s.leaf i) = x i then
    ∏ e : Fin (CubicConnectivitySkeleton.edgeCount (n + 3)),
      twoPointConnectivityENNReal d p (ψ (s.edge e).1) (ψ (s.edge e).2)
  else 0

/-- Translation invariance turns every row sum of the two-point kernel into the
susceptibility. -/
theorem tsum_twoPointConnectivityENNReal (d : ℕ) (p : unitInterval) (x : Cubic d) :
    ∑' y : Cubic d, twoPointConnectivityENNReal d p x y = susceptibility d p := by
  let T := cubicTranslationEquiv x cubicOrigin
  calc
    ∑' y : Cubic d, twoPointConnectivityENNReal d p x y =
        ∑' y : Cubic d, twoPointConnectivityENNReal d p cubicOrigin (T y) := by
      apply tsum_congr
      intro y
      rw [twoPointConnectivityENNReal_eq_ofReal,
        twoPointConnectivityENNReal_eq_ofReal]
      congr 1
      simpa [T] using (twoPointConnectivity_translate p x cubicOrigin x y).symm
    _ = ∑' y : Cubic d,
        twoPointConnectivityENNReal d p cubicOrigin y := by
      exact Equiv.tsum_eq T
        (fun y ↦ twoPointConnectivityENNReal d p cubicOrigin y)
    _ = susceptibility d p := by
      rw [susceptibility_eq_tsum_connection]
      apply tsum_congr
      intro y
      exact rfl

private theorem measure_labelledSkeletonEvent_le_weight
    {d n : ℕ} (p : unitInterval) (s : CubicConnectivitySkeleton (n + 3))
    (ψ : s.Vertex → Cubic d) (x : Fin (n + 3) → Cubic d) :
    bernoulliBondMeasure d p (labelledSkeletonEvent s ψ x) ≤
      skeletonConnectivityWeight p s ψ x := by
  classical
  by_cases hleaf : ∀ i, ψ (s.leaf i) = x i
  · simp only [labelledSkeletonEvent, skeletonConnectivityWeight, if_pos hleaf]
    let μ := bernoulliBondMeasure d p
    let J := (Finset.univ :
      Finset (Fin (CubicConnectivitySkeleton.edgeCount (n + 3))))
    let a := fun e : Fin (CubicConnectivitySkeleton.edgeCount (n + 3)) ↦
      ψ (s.edge e).1
    let b := fun e : Fin (CubicConnectivitySkeleton.edgeCount (n + 3)) ↦
      ψ (s.edge e).2
    have hbk := bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalks_le_prod
      d p J a b
    change μ (ExistsPairwiseDisjointOpenWalks d J a b) ≤ _
    rw [← MeasureTheory.ofReal_measureReal
      (μ := μ) (s := ExistsPairwiseDisjointOpenWalks d J a b)]
    calc
      ENNReal.ofReal (μ.real (ExistsPairwiseDisjointOpenWalks d J a b)) ≤
          ENNReal.ofReal (∏ e ∈ J,
            twoPointConnectivity d p (a e) (b e)) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [μ, J, a, b, twoPointConnectivity] using hbk
      _ = ∏ e : Fin (CubicConnectivitySkeleton.edgeCount (n + 3)),
            twoPointConnectivityENNReal d p (ψ (s.edge e).1) (ψ (s.edge e).2) := by
        rw [ENNReal.ofReal_prod_of_nonneg]
        · simp only [J, Finset.mem_univ, a, b]
          apply Finset.prod_congr rfl
          intro e _he
          exact (twoPointConnectivityENNReal_eq_ofReal d p _ _).symm
        · intro e _he
          exact twoPointConnectivity_nonneg d p (a e) (b e)
  · simp [labelledSkeletonEvent, skeletonConnectivityWeight, hleaf]

/-- Grimmett (6.93), in endpoint-safe `ℝ≥0∞` form: the probability of connecting all labelled
terminals is bounded by the sum, over all labelled trivalent skeletons and all placements of
their internal vertices, of the products of the two-point connectivities along skeleton edges. -/
theorem multiPointConnectivity_le_skeleton_sum
    (d n : ℕ) (p : unitInterval) (x : Fin (n + 3) → Cubic d) :
    bernoulliBondMeasure d p (orderedMultiPointConnectionEvent d n x) ≤
      ∑' s : CubicConnectivitySkeleton (n + 3),
        ∑' ψ : s.Vertex → Cubic d, skeletonConnectivityWeight p s ψ x := by
  let μ := bernoulliBondMeasure d p
  calc
    μ (orderedMultiPointConnectionEvent d n x) ≤
        μ (⋃ s : CubicConnectivitySkeleton (n + 3),
          ⋃ ψ : s.Vertex → Cubic d, labelledSkeletonEvent s ψ x) :=
      MeasureTheory.measure_mono
        (orderedMultiPointConnectionEvent_subset_iUnion_skeleton d n x)
    _ ≤ ∑' s : CubicConnectivitySkeleton (n + 3),
        ∑' ψ : s.Vertex → Cubic d, μ (labelledSkeletonEvent s ψ x) :=
      (MeasureTheory.measure_iUnion_le _).trans
        (ENNReal.tsum_le_tsum fun s ↦ MeasureTheory.measure_iUnion_le _)
    _ ≤ ∑' s : CubicConnectivitySkeleton (n + 3),
        ∑' ψ : s.Vertex → Cubic d, skeletonConnectivityWeight p s ψ x := by
      apply ENNReal.tsum_le_tsum
      intro s
      apply ENNReal.tsum_le_tsum
      intro ψ
      exact measure_labelledSkeletonEvent_le_weight p s ψ x

#print axioms cubicConnectivitySkeleton_card_eq
#print axioms exists_skeletonRealization_three
#print axioms exists_skeletonRealization
#print axioms orderedMultiPointConnectionEvent_subset_iUnion_skeleton
#print axioms multiPointConnectivity_le_skeleton_sum
#print axioms tsum_twoPointConnectivityENNReal

end Percolation
