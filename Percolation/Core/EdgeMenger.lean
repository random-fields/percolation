import Percolation.Core.TwoEdgeMenger
import Mathlib.Tactic

/-!
# Finite edge Menger infrastructure

This module generalizes the flow-decomposition half of `TwoEdgeMenger` from value two to an
arbitrary finite value.  The cut-to-flow direction is developed separately below; keeping the
two halves distinct makes the use of arbitrary-cardinality Menger in Chapters 7 and 11 auditable.
-/

namespace Percolation

open scoped BigOperators

namespace EdgeMenger

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- An antisymmetric integral unit-capacity flow of value `k` from `u` to `v`. -/
structure IsUnitFlow [Fintype V] (G : SimpleGraph V) (u v : V) (k : ℕ)
    (f : V → V → ℤ) : Prop where
  skew : ∀ x y, f x y = -f y x
  capacity : ∀ x y, f x y ∈ ({-1, 0, 1} : Set ℤ)
  support : ∀ ⦃x y⦄, f x y = 1 → G.Adj x y
  divergence : ∀ x, ∑ y : V, f x y =
    (k : ℤ) * ((if x = u then 1 else 0) - (if x = v then 1 else 0))

/-- The zero flow has value zero. -/
theorem isUnitFlow_zero [Fintype V] (G : SimpleGraph V) (u v : V) :
    IsUnitFlow G u v 0 (fun _ _ ↦ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    simp
  · intro x y
    simp
  · intro x y h
    simp at h
  · intro x
    simp

/-- Subtracting one directed path from a positive unit flow lowers its value by one. -/
theorem IsUnitFlow.sub_path [Fintype V] {u v : V} {k : ℕ} {f : V → V → ℤ}
    (hf : IsUnitFlow G u v (k + 1) f) (p : G.Walk u v)
    (hp : p.IsPath) (hpdir : ∀ a ∈ p.darts, f a.fst a.snd = 1) :
    IsUnitFlow G u v k (fun x y ↦ f x y - TwoEdgeMenger.walkFlow p x y) := by
  let f' : V → V → ℤ := fun x y ↦ f x y - TwoEdgeMenger.walkFlow p x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    change f x y - TwoEdgeMenger.walkFlow p x y =
      -(f y x - TwoEdgeMenger.walkFlow p y x)
    rw [hf.skew x y, TwoEdgeMenger.walkFlow_skew p x y]
    omega
  · intro x y
    exact TwoEdgeMenger.sub_walkFlow_mem_neg_one_zero_one hp.isTrail hf.skew
      hf.capacity hpdir x y
  · intro x y hxy
    have hpvals : TwoEdgeMenger.walkFlow p x y = -1 ∨
        TwoEdgeMenger.walkFlow p x y = 0 ∨ TwoEdgeMenger.walkFlow p x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        TwoEdgeMenger.walkFlow_mem_neg_one_zero_one_of_isTrail hp.isTrail x y
    rcases hpvals with hpflow | hpflow | hpflow
    · have hfneg := TwoEdgeMenger.flow_eq_neg_one_of_walkFlow_eq_neg_one hp.isTrail
          hf.skew hpdir hpflow
      simp [hfneg, hpflow] at hxy
    · apply hf.support
      simpa [f', hpflow] using hxy
    · have hfone := TwoEdgeMenger.flow_eq_one_of_walkFlow_eq_one hp.isTrail hpdir hpflow
      simp [hfone, hpflow] at hxy
  · intro x
    change (∑ y : V, (f x y - TwoEdgeMenger.walkFlow p x y)) = _
    rw [Finset.sum_sub_distrib, hf.divergence x, TwoEdgeMenger.sum_walkFlow p x]
    push_cast
    ring

/-- Adding a residual path to a value-`k` unit flow produces a value-`k+1` unit flow. -/
theorem IsUnitFlow.add_residual_path [Fintype V] {u v : V} {k : ℕ}
    {f : V → V → ℤ} (hf : IsUnitFlow G u v k f) (q : G.Walk u v)
    (hq : q.IsPath) (hqres : ∀ a ∈ q.darts, f a.fst a.snd ≤ 0) :
    IsUnitFlow G u v (k + 1) (fun x y ↦ f x y + TwoEdgeMenger.walkFlow q x y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    change f x y + TwoEdgeMenger.walkFlow q x y =
      -(f y x + TwoEdgeMenger.walkFlow q y x)
    rw [hf.skew x y, TwoEdgeMenger.walkFlow_skew q x y]
    omega
  · intro x y
    have hfvals : f x y = -1 ∨ f x y = 0 ∨ f x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf.capacity x y
    have hqvals : TwoEdgeMenger.walkFlow q x y = -1 ∨
        TwoEdgeMenger.walkFlow q x y = 0 ∨ TwoEdgeMenger.walkFlow q x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        TwoEdgeMenger.walkFlow_mem_neg_one_zero_one_of_isTrail hq.isTrail x y
    rcases hqvals with hqflow | hqflow | hqflow
    · have hqrev : TwoEdgeMenger.walkFlow q y x = 1 := by
        rw [TwoEdgeMenger.walkFlow_skew q y x, hqflow]
        omega
      have hfresrev : f y x ≤ 0 :=
        TwoEdgeMenger.property_of_walkFlow_eq_one hq.isTrail
          (fun a b ↦ f a b ≤ 0) hqres hqrev
      have hfres : 0 ≤ f x y := by rw [hf.skew y x] at hfresrev; omega
      rcases hfvals with h | h | h <;> simp [h, hqflow] <;> omega
    · rcases hfvals with h | h | h <;> simp [h, hqflow]
    · have hfres : f x y ≤ 0 :=
        TwoEdgeMenger.property_of_walkFlow_eq_one hq.isTrail
          (fun a b ↦ f a b ≤ 0) hqres hqflow
      rcases hfvals with h | h | h <;> simp [h, hqflow] <;> omega
  · intro x y hxy
    have hfvals : f x y = -1 ∨ f x y = 0 ∨ f x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf.capacity x y
    have hqvals : TwoEdgeMenger.walkFlow q x y = -1 ∨
        TwoEdgeMenger.walkFlow q x y = 0 ∨ TwoEdgeMenger.walkFlow q x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        TwoEdgeMenger.walkFlow_mem_neg_one_zero_one_of_isTrail hq.isTrail x y
    rcases hfvals with hfxy | hfxy | hfxy <;>
      rcases hqvals with hqxy | hqxy | hqxy
    all_goals try {simp [hfxy, hqxy] at hxy}
    · exact TwoEdgeMenger.property_of_walkFlow_eq_one hq.isTrail G.Adj
        (fun a _ha ↦ a.adj) hqxy
    · exact hf.support hfxy
  · intro x
    change (∑ y : V, (f x y + TwoEdgeMenger.walkFlow q x y)) = _
    rw [Finset.sum_add_distrib, hf.divergence x, TwoEdgeMenger.sum_walkFlow q x]
    push_cast
    ring

/-- A path directed by the residual flow cannot share an unoriented edge with the path that was
subtracted. -/
theorem edges_disjoint_of_residual_direction [Fintype V] {u v : V}
    {f : V → V → ℤ} (hskew : ∀ x y, f x y = -f y x)
    (p q : G.Walk u v) (hp : p.IsPath)
    (hpdir : ∀ a ∈ p.darts, f a.fst a.snd = 1)
    (hqdir : ∀ a ∈ q.darts,
      f a.fst a.snd - TwoEdgeMenger.walkFlow p a.fst a.snd = 1) :
    p.edges.Disjoint q.edges := by
  rw [List.disjoint_left]
  intro e hep heq
  rw [SimpleGraph.Walk.edges] at hep heq
  rcases List.mem_map.mp hep with ⟨a, ha, hae⟩
  rcases List.mem_map.mp heq with ⟨b, hb, hbe⟩
  have hedge : s(a.fst, a.snd) = s(b.fst, b.snd) := by
    simpa [SimpleGraph.Dart.edge] using hae.trans hbe.symm
  have hpflow : TwoEdgeMenger.walkFlow p a.fst a.snd = 1 :=
    TwoEdgeMenger.walkFlow_eq_one_of_mem_darts_of_isTrail hp.isTrail ha
  have hpvalue : f a.fst a.snd = 1 := hpdir a ha
  rcases Sym2.eq_iff.mp hedge with hsame | hreverse
  · have hqvalue := hqdir b hb
    rw [hsame.1, hsame.2] at hpflow hpvalue
    simp [hpflow, hpvalue] at hqvalue
  · have hqvalue := hqdir b hb
    have hpflow_rev : TwoEdgeMenger.walkFlow p a.snd a.fst = -1 := by
      rw [TwoEdgeMenger.walkFlow_skew p a.snd a.fst, hpflow]
    have hpvalue_rev : f a.snd a.fst = -1 := by
      rw [hskew a.snd a.fst, hpvalue]
    rw [hreverse.1, hreverse.2] at hpflow_rev hpvalue_rev
    simp [hpflow_rev, hpvalue_rev] at hqvalue

/-- Every integral unit-capacity flow of value `k` decomposes into `k` pairwise edge-disjoint
simple paths, each oriented along a positive-flow dart. -/
theorem exists_pairwise_edgeDisjoint_paths_of_unitFlow [Fintype V]
    {u v : V} {k : ℕ} (f : V → V → ℤ) (hf : IsUnitFlow G u v k f) :
    ∃ P : Fin k → G.Walk u v,
      (∀ i, (P i).IsPath) ∧
      (Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) ∧
      ∀ i a, a ∈ (P i).darts → f a.fst a.snd = 1 := by
  classical
  induction k generalizing f with
  | zero =>
      exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i,
        fun i ↦ Fin.elim0 i⟩
  | succ k ih =>
      have hchain := TwoEdgeMenger.exists_positive_reflTransGen f hf.skew hf.capacity
        (k := (k + 1 : ℕ)) (by positivity) hf.divergence
      obtain ⟨w, hwdir⟩ := TwoEdgeMenger.exists_walk_of_reflTransGen hf.support hchain
      let p : G.Walk u v := w.toPath
      have hp : p.IsPath := w.toPath.2
      have hpdir : ∀ a ∈ p.darts, f a.fst a.snd = 1 := by
        intro a ha
        exact hwdir a (SimpleGraph.Walk.darts_toPath_subset w ha)
      let f' : V → V → ℤ := fun x y ↦ f x y - TwoEdgeMenger.walkFlow p x y
      have hf' : IsUnitFlow G u v k f' := by
        simpa [f'] using hf.sub_path p hp hpdir
      obtain ⟨Q, hQpath, hQdisj, hQdir⟩ := ih f' hf'
      let P : Fin (k + 1) → G.Walk u v := Fin.cases p Q
      refine ⟨P, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases hp (fun j ↦ ?_) i
        exact hQpath j
      · intro i j hij
        refine Fin.cases (motive := fun i ↦ ∀ j, i ≠ j →
          (P i).edges.Disjoint (P j).edges) ?_ (fun i' ↦ ?_) i j hij
        · intro j hne
          refine Fin.cases (motive := fun j ↦ (0 : Fin (k + 1)) ≠ j →
            (P 0).edges.Disjoint (P j).edges) ?_ (fun j' _hne ↦ ?_) j hne
          · intro h
            exact (h rfl).elim
          · exact edges_disjoint_of_residual_direction hf.skew p (Q j') hp hpdir
              (fun a ha ↦ hQdir j' a ha)
        · intro j hne
          refine Fin.cases (motive := fun j ↦ Fin.succ i' ≠ j →
            (P (Fin.succ i')).edges.Disjoint (P j).edges)
            (fun _hne ↦ ?_) (fun j' hne' ↦ ?_) j hne
          · exact (edges_disjoint_of_residual_direction hf.skew p (Q i') hp hpdir
              (fun a ha ↦ hQdir i' a ha)).symm
          · apply hQdisj
            intro heq
            apply hne'
            exact congrArg Fin.succ heq
      · intro i
        refine Fin.cases (fun a ha ↦ hpdir a ha) (fun j a ha ↦ ?_) i
        have hres := hQdir j a ha
        have hqflow : f' a.fst a.snd = 1 := hres
        dsimp [f'] at hqflow
        have hpvals : TwoEdgeMenger.walkFlow p a.fst a.snd = -1 ∨
            TwoEdgeMenger.walkFlow p a.fst a.snd = 0 ∨
              TwoEdgeMenger.walkFlow p a.fst a.snd = 1 := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
            TwoEdgeMenger.walkFlow_mem_neg_one_zero_one_of_isTrail hp.isTrail a.fst a.snd
        rcases hpvals with hpflow | hpflow | hpflow
        · have hfneg := TwoEdgeMenger.flow_eq_neg_one_of_walkFlow_eq_neg_one hp.isTrail
            hf.skew hpdir hpflow
          simp [hpflow, hfneg] at hqflow
        · simpa [hpflow] using hqflow
        · have hfone := TwoEdgeMenger.flow_eq_one_of_walkFlow_eq_one hp.isTrail hpdir hpflow
          simp [hpflow, hfone] at hqflow

/-- If a value-`k` unit flow exists and the graph is `(k+1)`-edge-reachable, the residual
network contains another source-to-sink path. -/
theorem exists_residual_path_of_isEdgeReachable_succ [Fintype V]
    {u v : V} {k : ℕ} {f : V → V → ℤ}
    (hf : IsUnitFlow G u v k f) (hreach : G.IsEdgeReachable (k + 1) u v) :
    ∃ q : G.Walk u v, q.IsPath ∧ ∀ a ∈ q.darts, f a.fst a.snd ≤ 0 := by
  classical
  let R : V → V → Prop := fun x y ↦ G.Adj x y ∧ f x y ≤ 0
  by_contra hno
  have hnochain : ¬Relation.ReflTransGen R u v := by
    intro hchain
    obtain ⟨w, hw⟩ := TwoEdgeMenger.exists_walk_of_reflTransGen
      (fun {_ _} h ↦ h.1) hchain
    let q : G.Walk u v := w.toPath
    have hqdir : ∀ a ∈ q.darts, f a.fst a.snd ≤ 0 := by
      intro a ha
      exact (hw a (SimpleGraph.Walk.darts_toPath_subset w ha)).2
    exact hno ⟨q, w.toPath.2, hqdir⟩
  let S : Finset V := Finset.univ.filter fun x ↦ Relation.ReflTransGen R u x
  let O : Finset V := Finset.univ \ S
  have huS : u ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, Relation.ReflTransGen.refl⟩
  have hvS : v ∉ S := by simp [S, hnochain]
  have hcross : ∀ x ∈ S, ∀ y ∈ O, G.Adj x y → f x y = 1 := by
    intro x hx y hy hxy
    have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
    have hnotle : ¬f x y ≤ 0 := by
      intro hle
      apply hyS
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ y, Relation.ReflTransGen.tail hx.2 ⟨hxy, hle⟩⟩
    have hvals : f x y = -1 ∨ f x y = 0 ∨ f x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf.capacity x y
    rcases hvals with h | h | h <;> omega
  have hcross_zero : ∀ x ∈ S, ∀ y ∈ O, ¬G.Adj x y → f x y = 0 := by
    intro x hx y hy hxy
    have hvals : f x y = -1 ∨ f x y = 0 ∨ f x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf.capacity x y
    rcases hvals with hneg | hzero | hpos
    · have hrev : f y x = 1 := by rw [hf.skew y x, hneg]; omega
      exact (hxy (hf.support hrev).symm).elim
    · exact hzero
    · exact (hxy (hf.support hpos)).elim
  let internal : ℤ := ∑ x ∈ S, ∑ y ∈ S, f x y
  let outgoing : ℤ := ∑ x ∈ S, ∑ y ∈ O, f x y
  have hinternal_neg : internal = -internal := by
    calc
      internal = ∑ y ∈ S, ∑ x ∈ S, f x y := by
        simp only [internal]
        exact Finset.sum_comm
      _ = ∑ y ∈ S, ∑ x ∈ S, -f y x := by
        apply Finset.sum_congr rfl
        intro y _hy
        apply Finset.sum_congr rfl
        intro x _hx
        exact hf.skew x y
      _ = -internal := by simp only [Finset.sum_neg_distrib, internal]
  have hinternal : internal = 0 := by omega
  have hsplit : (∑ x ∈ S, ∑ y : V, f x y) = internal + outgoing := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [show (∑ y : V, f x y) = ∑ y ∈ Finset.univ, f x y by rfl]
    rw [← Finset.sum_sdiff S.subset_univ]
    exact add_comm _ _
  have htotal : (∑ x ∈ S, ∑ y : V, f x y) = (k : ℤ) := by
    simp_rw [hf.divergence]
    calc
      (∑ x ∈ S, (k : ℤ) *
          ((if x = u then 1 else 0) - (if x = v then 1 else 0))) =
          (k : ℤ) * ((∑ x ∈ S, if x = u then 1 else 0) -
            ∑ x ∈ S, if x = v then 1 else 0) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = (k : ℤ) := by simp [huS, hvS]
  have houtgoing : outgoing = (k : ℤ) := by
    rw [hsplit, hinternal, zero_add] at htotal
    exact htotal
  let cutPairs : Finset (V × V) :=
    (S ×ˢ O).filter fun q ↦ G.Adj q.1 q.2
  have hcutPairsCard : cutPairs.card = k := by
    have hsum : (∑ q ∈ cutPairs, f q.1 q.2) = outgoing := by
      simp only [cutPairs, Finset.sum_filter, Finset.sum_product, outgoing]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : G.Adj x y
      · simp [hxy, hcross x hx y hy hxy]
      · simp [hxy, hcross_zero x hx y hy hxy]
    have hones : (∑ q ∈ cutPairs, f q.1 q.2) = cutPairs.card := by
      calc
        (∑ q ∈ cutPairs, f q.1 q.2) = ∑ _q ∈ cutPairs, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro q hq
          have hq' := Finset.mem_filter.mp hq
          have hmem := Finset.mem_product.mp hq'.1
          exact hcross q.1 hmem.1 q.2 hmem.2 hq'.2
        _ = cutPairs.card := by simp
    have hcardZ : (cutPairs.card : ℤ) = (k : ℤ) :=
      hones.symm.trans (hsum.trans houtgoing)
    exact_mod_cast hcardZ
  let cutEdges : Finset (Sym2 V) := cutPairs.image fun q ↦ s(q.1, q.2)
  have hpairInjective : Set.InjOn (fun q : V × V ↦ s(q.1, q.2)) cutPairs := by
    intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have haMem := Finset.mem_product.mp ha'.1
    have hbMem := Finset.mem_product.mp hb'.1
    rcases Sym2.eq_iff.mp hab with hsame | hreverse
    · exact Prod.ext hsame.1 hsame.2
    · exfalso
      have haS : a.1 ∈ S := haMem.1
      have hbNotS : b.2 ∉ S := (Finset.mem_sdiff.mp hbMem.2).2
      exact hbNotS (hreverse.1 ▸ haS)
  have hcutEdgesCard : cutEdges.card = k := by
    change (cutPairs.image fun q ↦ s(q.1, q.2)).card = k
    rw [Finset.card_image_iff.mpr hpairInjective, hcutPairsCard]
  have hdeleted : ¬(G.deleteEdges (cutEdges : Set (Sym2 V))).Reachable u v := by
    rintro ⟨w⟩
    have hexit : ∃ j : ℕ, j ≤ w.length ∧ w.getVert j ∉ S :=
      ⟨w.length, le_rfl, by simpa using hvS⟩
    let j := Nat.find hexit
    have hj : j ≤ w.length ∧ w.getVert j ∉ S := Nat.find_spec hexit
    have hjpos : 0 < j := by
      by_contra hj0
      have : j = 0 := Nat.eq_zero_of_not_pos hj0
      exact hj.2 (by simpa [this] using huS)
    have hprevS : w.getVert (j - 1) ∈ S := by
      by_contra hprev
      exact Nat.find_min hexit (by omega) ⟨by omega, hprev⟩
    have hadjDel := w.adj_getVert_succ (i := j - 1) (by omega)
    have hadj : G.Adj (w.getVert (j - 1)) (w.getVert j) := by
      simpa [Nat.sub_add_cancel hjpos] using (SimpleGraph.deleteEdges_adj.mp hadjDel).1
    have hnextO : w.getVert j ∈ O := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj.2⟩
    have hpair : (w.getVert (j - 1), w.getVert j) ∈ cutPairs := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hprevS, hnextO⟩, hadj⟩
    have hedge : s(w.getVert (j - 1), w.getVert j) ∈ cutEdges := by
      exact Finset.mem_image.mpr ⟨_, hpair, rfl⟩
    exact (SimpleGraph.deleteEdges_adj.mp hadjDel).2 <| by
      simpa [Nat.sub_add_cancel hjpos] using hedge
  have hcutlt : (cutEdges : Set (Sym2 V)).encard < (k + 1 : ℕ) := by
    rw [Set.encard_coe_eq_coe_finsetCard, hcutEdgesCard]
    exact ENat.coe_lt_coe.mpr (Nat.lt_succ_self k)
  exact hdeleted (hreach hcutlt)

/-- Finite cut-survival produces an integral unit-capacity flow of the same value.  This is the
augmenting-path direction of finite edge Menger. -/
theorem exists_unitFlow_of_isEdgeReachable [Fintype V]
    {u v : V} {k : ℕ} (hreach : G.IsEdgeReachable k u v) :
    ∃ f : V → V → ℤ, IsUnitFlow G u v k f := by
  classical
  induction k with
  | zero => exact ⟨fun _ _ ↦ 0, isUnitFlow_zero G u v⟩
  | succ k ih =>
      have hprev : G.IsEdgeReachable k u v := hreach.anti (Nat.le_succ k)
      obtain ⟨f, hf⟩ := ih hprev
      obtain ⟨q, hq, hqres⟩ :=
        exists_residual_path_of_isEdgeReachable_succ hf hreach
      let f' : V → V → ℤ := fun x y ↦ f x y + TwoEdgeMenger.walkFlow q x y
      exact ⟨f', by simpa [f'] using hf.add_residual_path q hq hqres⟩

omit [DecidableEq V] in
/-- Any family of `k` pairwise edge-disjoint walks survives deletion of fewer than `k` edges. -/
theorem isEdgeReachable_of_pairwise_edgeDisjoint_walks [Fintype V]
    {u v : V} {k : ℕ} (P : Fin k → G.Walk u v)
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) :
    G.IsEdgeReachable k u v := by
  classical
  intro s hs
  have hsFinite : s.Finite := Set.finite_of_encard_le_coe hs.le
  by_contra hno
  have hall : ∀ i : Fin k, ∃ e, e ∈ (P i).edges ∧ e ∈ s := by
    intro i
    by_contra hi
    push Not at hi
    apply hno
    exact ⟨(P i).toDeleteEdges s (fun e he ↦ hi e he)⟩
  let chosen : Fin k → Sym2 V := fun i ↦ Classical.choose (hall i)
  have chosen_mem_walk (i : Fin k) : chosen i ∈ (P i).edges :=
    (Classical.choose_spec (hall i)).1
  have chosen_mem_s (i : Fin k) : chosen i ∈ s :=
    (Classical.choose_spec (hall i)).2
  let sf : Finset (Sym2 V) := hsFinite.toFinset
  let F : Fin k → {e // e ∈ sf} := fun i ↦
    ⟨chosen i, by simpa [sf] using chosen_mem_s i⟩
  have hF : Function.Injective F := by
    intro i j hij
    by_contra hne
    have hchosen : chosen i = chosen j := Subtype.ext_iff.mp hij
    exact List.disjoint_left.mp (hP hne) (chosen_mem_walk i)
      (hchosen ▸ chosen_mem_walk j)
  have hkcard : k ≤ sf.card := by
    simpa [F] using Fintype.card_le_of_injective F hF
  have hcardlt : sf.card < k := by
    rw [← ENat.coe_lt_coe]
    rw [show (sf.card : ℕ∞) = s.encard by
      exact hsFinite.encard_eq_coe_toFinset_card.symm]
    exact hs
  omega

omit [DecidableEq V] in
/-- The easy direction of finite edge Menger: `k` pairwise edge-disjoint paths imply
`k`-edge-reachability. -/
theorem isEdgeReachable_of_pairwise_edgeDisjoint_paths [Fintype V]
    {u v : V} {k : ℕ} (P : Fin k → G.Walk u v)
    (_hpath : ∀ i, (P i).IsPath)
    (hP : Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges) :
    G.IsEdgeReachable k u v :=
  isEdgeReachable_of_pairwise_edgeDisjoint_walks P hP

/-- **Finite arbitrary-cardinality edge Menger theorem.** Survival after deletion of every set
of fewer than `k` edges is equivalent to the existence of `k` pairwise edge-disjoint paths. -/
theorem isEdgeReachable_iff_exists_pairwise_edgeDisjoint_paths [Fintype V]
    {u v : V} {k : ℕ} :
    G.IsEdgeReachable k u v ↔
      ∃ P : Fin k → G.Walk u v,
        (∀ i, (P i).IsPath) ∧
          Pairwise fun i j ↦ (P i).edges.Disjoint (P j).edges := by
  constructor
  · intro hreach
    obtain ⟨f, hf⟩ := exists_unitFlow_of_isEdgeReachable hreach
    obtain ⟨P, hPpath, hPdisj, _hPdir⟩ :=
      exists_pairwise_edgeDisjoint_paths_of_unitFlow f hf
    exact ⟨P, hPpath, hPdisj⟩
  · rintro ⟨P, hPpath, hPdisj⟩
    exact isEdgeReachable_of_pairwise_edgeDisjoint_paths P hPpath hPdisj

end EdgeMenger

end Percolation
