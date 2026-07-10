import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A finite two-edge Menger theorem

Mathlib defines two-edge reachability by survival after deletion of any one edge, but does not
currently provide the equivalent pair of edge-disjoint paths.  Chapter 5 needs precisely this
special case, so this file proves it for finite simple graphs using a unit-capacity augmenting
path argument.
-/

namespace Percolation

open scoped BigOperators

namespace TwoEdgeMenger

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- The antisymmetric unit flow carried by the oriented edge `a → b`. -/
def edgeUnit (a b x y : V) : ℤ :=
  if x = a ∧ y = b then 1 else if x = b ∧ y = a then -1 else 0

theorem edgeUnit_skew (a b x y : V) (hab : a ≠ b) :
    edgeUnit a b x y = -edgeUnit a b y x := by
  simp only [edgeUnit]
  split_ifs <;> simp_all

/-- The integral antisymmetric flow carried by a graph walk. -/
def walkFlow {u v : V} : G.Walk u v → V → V → ℤ
  | .nil => fun _ _ ↦ 0
  | .cons (u := u) (v := v) huv p => fun x y ↦ edgeUnit u v x y + walkFlow p x y

theorem walkFlow_skew {u v : V} (w : G.Walk u v) (x y : V) :
    walkFlow w x y = -walkFlow w y x := by
  induction w with
  | nil => simp [walkFlow]
  | @cons u v z huv p ih =>
      change edgeUnit u v x y + walkFlow p x y =
        -(edgeUnit u v y x + walkFlow p y x)
      rw [edgeUnit_skew u v x y huv.ne, ih]
      omega

theorem sum_edgeUnit [Fintype V] (a b x : V) (hab : a ≠ b) :
    ∑ y : V, edgeUnit a b x y = (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
  classical
  by_cases hxa : x = a
  · subst x
    simp [edgeUnit, hab]
  · by_cases hxb : x = b
    · subst x
      simp [edgeUnit, hxa]
    · simp [edgeUnit, hxa, hxb]

/-- Divergence of a walk flow: one unit leaves the start and enters the endpoint. -/
theorem sum_walkFlow [Fintype V] {u v : V} (w : G.Walk u v) (x : V) :
    ∑ y : V, walkFlow w x y =
      (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  induction w with
  | nil => simp [walkFlow]
  | @cons u v z huv p ih =>
      rw [show (∑ y : V, walkFlow (SimpleGraph.Walk.cons huv p) x y) =
          (∑ y : V, edgeUnit u v x y) + ∑ y : V, walkFlow p x y by
        simp only [walkFlow, Finset.sum_add_distrib]]
      rw [sum_edgeUnit u v x huv.ne, ih]
      by_cases hxu : x = u <;> by_cases hxv : x = v <;> by_cases hxz : x = z <;>
        simp_all

theorem edgeUnit_eq_zero_of_sym2_ne {a b x y : V} (h : s(x, y) ≠ s(a, b)) :
    edgeUnit a b x y = 0 := by
  simp only [edgeUnit]
  split_ifs with h₁ h₂
  · exact (h (Sym2.eq_iff.mpr (Or.inl h₁))).elim
  · exact (h (Sym2.eq_iff.mpr (Or.inr h₂))).elim
  · rfl

theorem walkFlow_eq_zero_of_not_mem_edges {u v x y : V} (w : G.Walk u v)
    (h : s(x, y) ∉ w.edges) : walkFlow w x y = 0 := by
  induction w with
  | nil => simp [walkFlow]
  | @cons a b z hab p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at h
      change edgeUnit a b x y + walkFlow p x y = 0
      rw [edgeUnit_eq_zero_of_sym2_ne h.1, ih h.2, zero_add]

/-- A trail carries at most one unit of flow in either direction of any edge. -/
theorem walkFlow_mem_neg_one_zero_one_of_isTrail {u v : V} {w : G.Walk u v}
    (hw : w.IsTrail) (x y : V) : walkFlow w x y ∈ ({-1, 0, 1} : Set ℤ) := by
  induction w with
  | nil => simp [walkFlow]
  | @cons a b z hab p ih =>
      have hnodup := hw.edges_nodup
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
      by_cases hxy : s(x, y) = s(a, b)
      · have htail : walkFlow p x y = 0 :=
          walkFlow_eq_zero_of_not_mem_edges p (hxy ▸ hnodup.1)
        change edgeUnit a b x y + walkFlow p x y ∈ ({-1, 0, 1} : Set ℤ)
        rw [htail, add_zero]
        rcases Sym2.eq_iff.mp hxy with h | h
        · rcases h with ⟨rfl, rfl⟩
          simp [edgeUnit]
        · rcases h with ⟨rfl, rfl⟩
          simp [edgeUnit, hab.ne]
      · change edgeUnit a b x y + walkFlow p x y ∈ ({-1, 0, 1} : Set ℤ)
        rw [edgeUnit_eq_zero_of_sym2_ne hxy, zero_add]
        exact ih (show p.IsTrail by exact ⟨hnodup.2⟩)

theorem walkFlow_eq_one_of_mem_darts_of_isTrail {u v : V} {w : G.Walk u v}
    (hw : w.IsTrail) {a : G.Dart} (ha : a ∈ w.darts) :
    walkFlow w a.fst a.snd = 1 := by
  induction w with
  | nil => simp at ha
  | @cons x y z hxy p ih =>
      have hnodup := hw.edges_nodup
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
      simp only [SimpleGraph.Walk.darts_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · change edgeUnit x y x y + walkFlow p x y = 1
        rw [walkFlow_eq_zero_of_not_mem_edges p hnodup.1]
        simp [edgeUnit]
      · have haedge : a.edge ∈ p.edges := by
          rw [SimpleGraph.Walk.edges]
          exact List.mem_map.mpr ⟨a, ha, rfl⟩
        have hne : s(a.fst, a.snd) ≠ s(x, y) := by
          intro heq
          exact hnodup.1 (heq ▸ haedge)
        change edgeUnit x y a.fst a.snd + walkFlow p a.fst a.snd = 1
        rw [edgeUnit_eq_zero_of_sym2_ne hne, zero_add]
        exact ih (show p.IsTrail by exact ⟨hnodup.2⟩) ha

theorem exists_mem_darts_of_walkFlow_eq_one_of_isTrail {u v : V} {w : G.Walk u v}
    (hw : w.IsTrail) {x y : V} (hflow : walkFlow w x y = 1) :
    ∃ a ∈ w.darts, a.fst = x ∧ a.snd = y := by
  induction w with
  | nil => simp [walkFlow] at hflow
  | @cons a b z hab p ih =>
      have hnodup := hw.edges_nodup
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
      change edgeUnit a b x y + walkFlow p x y = 1 at hflow
      by_cases hxy : s(x, y) = s(a, b)
      · have hpzero : walkFlow p x y = 0 :=
          walkFlow_eq_zero_of_not_mem_edges p (hxy ▸ hnodup.1)
        rw [hpzero, add_zero] at hflow
        rcases Sym2.eq_iff.mp hxy with h | h
        · rcases h with ⟨rfl, rfl⟩
          exact ⟨⟨(x, y), hab⟩, by simp⟩
        · rcases h with ⟨rfl, rfl⟩
          simp [edgeUnit, hab.ne] at hflow
      · rw [edgeUnit_eq_zero_of_sym2_ne hxy, zero_add] at hflow
        obtain ⟨c, hc, hcxy⟩ :=
          ih (show p.IsTrail by exact ⟨hnodup.2⟩) hflow
        exact ⟨c, by simp [hc], hcxy⟩

/-- Positive integral flow cannot be trapped away from its sink. -/
theorem exists_positive_reflTransGen [Fintype V] {u v : V} (f : V → V → ℤ)
    (hskew : ∀ x y, f x y = -f y x)
    (hcap : ∀ x y, f x y ∈ ({-1, 0, 1} : Set ℤ))
    {k : ℤ} (hk : 0 < k)
    (hdiv : ∀ x, ∑ y : V, f x y =
      k * ((if x = u then 1 else 0) - (if x = v then 1 else 0))) :
    Relation.ReflTransGen (fun x y ↦ f x y = 1) u v := by
  classical
  by_contra hnot
  let S : Finset V := Finset.univ.filter fun x ↦
    Relation.ReflTransGen (fun a b ↦ f a b = 1) u x
  have huS : u ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, Relation.ReflTransGen.refl⟩
  have hvS : v ∉ S := by simp [S, hnot]
  have hout_nonpos : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, f x y ≤ 0 := by
    intro x hx y hy
    have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
    have hne : f x y ≠ 1 := by
      intro hxy
      apply hyS
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ y, Relation.ReflTransGen.tail hx.2 hxy⟩
    have hvals : f x y = -1 ∨ f x y = 0 ∨ f x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcap x y
    rcases hvals with h | h | h <;> omega
  let internal : ℤ := ∑ x ∈ S, ∑ y ∈ S, f x y
  let outgoing : ℤ := ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, f x y
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
        exact hskew x y
      _ = -internal := by
        simp only [Finset.sum_neg_distrib, internal]
  have hinternal : internal = 0 := by omega
  have houtgoing : outgoing ≤ 0 := by
    exact Finset.sum_nonpos fun x hx ↦ Finset.sum_nonpos fun y hy ↦
      hout_nonpos x hx y hy
  have hsplit : (∑ x ∈ S, ∑ y : V, f x y) = internal + outgoing := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [show (∑ y : V, f x y) = ∑ y ∈ Finset.univ, f x y by rfl]
    rw [← Finset.sum_sdiff S.subset_univ]
    exact add_comm _ _
  have htotal : (∑ x ∈ S, ∑ y : V, f x y) = k := by
    simp_rw [hdiv]
    calc
      (∑ x ∈ S,
          k * ((if x = u then 1 else 0) - (if x = v then 1 else 0))) =
          k * ((∑ x ∈ S, if x = u then 1 else 0) -
            ∑ x ∈ S, if x = v then 1 else 0) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = k := by simp [huS, hvS]
  have : k ≤ 0 := by
    rw [hsplit, hinternal, zero_add] at htotal
    omega
  omega

omit [DecidableEq V] in
theorem nonempty_walk_of_reflTransGen {R : V → V → Prop}
    (hR : ∀ ⦃x y⦄, R x y → G.Adj x y) {u v : V}
    (h : Relation.ReflTransGen R u v) : Nonempty (G.Walk u v) := by
  induction h with
  | refl => exact ⟨.nil⟩
  | tail _ hxy ih =>
      obtain ⟨w⟩ := ih
      exact ⟨w.concat (hR hxy)⟩

omit [DecidableEq V] in
theorem exists_walk_of_reflTransGen {R : V → V → Prop}
    (hR : ∀ ⦃x y⦄, R x y → G.Adj x y) {u v : V}
    (h : Relation.ReflTransGen R u v) :
    ∃ w : G.Walk u v, ∀ a ∈ w.darts, R a.fst a.snd := by
  induction h with
  | refl => exact ⟨.nil, by simp⟩
  | @tail b c _ hbc ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨w.concat (hR hbc), ?_⟩
      intro a ha
      rw [SimpleGraph.Walk.darts_concat, List.concat_eq_append] at ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hw a ha
      · exact hbc

theorem flow_eq_one_of_walkFlow_eq_one {u v : V} {w : G.Walk u v}
    (hw : w.IsTrail) {f : V → V → ℤ}
    (hdir : ∀ a ∈ w.darts, f a.fst a.snd = 1) {x y : V}
    (hflow : walkFlow w x y = 1) : f x y = 1 := by
  induction w with
  | nil => simp [walkFlow] at hflow
  | @cons a b z hab p ih =>
      have hnodup := hw.edges_nodup
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
      have hhead : f a b = 1 := hdir ⟨(a, b), hab⟩ (by simp)
      have htail : ∀ c ∈ p.darts, f c.fst c.snd = 1 := by
        intro c hc
        exact hdir c (by simp [hc])
      change edgeUnit a b x y + walkFlow p x y = 1 at hflow
      by_cases hxy : s(x, y) = s(a, b)
      · have hpzero : walkFlow p x y = 0 :=
          walkFlow_eq_zero_of_not_mem_edges p (hxy ▸ hnodup.1)
        rw [hpzero, add_zero] at hflow
        rcases Sym2.eq_iff.mp hxy with h | h
        · rcases h with ⟨rfl, rfl⟩
          exact hhead
        · rcases h with ⟨rfl, rfl⟩
          simp [edgeUnit, hab.ne] at hflow
      · rw [edgeUnit_eq_zero_of_sym2_ne hxy, zero_add] at hflow
        exact ih (show p.IsTrail by exact ⟨hnodup.2⟩) htail hflow

theorem property_of_walkFlow_eq_one {u v : V} {w : G.Walk u v}
    (hw : w.IsTrail) (P : V → V → Prop)
    (hdir : ∀ a ∈ w.darts, P a.fst a.snd) {x y : V}
    (hflow : walkFlow w x y = 1) : P x y := by
  induction w with
  | nil => simp [walkFlow] at hflow
  | @cons a b z hab p ih =>
      have hnodup := hw.edges_nodup
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
      have hhead : P a b := hdir ⟨(a, b), hab⟩ (by simp)
      have htail : ∀ c ∈ p.darts, P c.fst c.snd := by
        intro c hc
        exact hdir c (by simp [hc])
      change edgeUnit a b x y + walkFlow p x y = 1 at hflow
      by_cases hxy : s(x, y) = s(a, b)
      · have hpzero : walkFlow p x y = 0 :=
          walkFlow_eq_zero_of_not_mem_edges p (hxy ▸ hnodup.1)
        rw [hpzero, add_zero] at hflow
        rcases Sym2.eq_iff.mp hxy with h | h
        · rcases h with ⟨rfl, rfl⟩
          exact hhead
        · rcases h with ⟨rfl, rfl⟩
          simp [edgeUnit, hab.ne] at hflow
      · rw [edgeUnit_eq_zero_of_sym2_ne hxy, zero_add] at hflow
        exact ih (show p.IsTrail by exact ⟨hnodup.2⟩) htail hflow

theorem flow_eq_neg_one_of_walkFlow_eq_neg_one {u v : V} {w : G.Walk u v}
    (hw : w.IsTrail) {f : V → V → ℤ} (hskew : ∀ x y, f x y = -f y x)
    (hdir : ∀ a ∈ w.darts, f a.fst a.snd = 1) {x y : V}
    (hflow : walkFlow w x y = -1) : f x y = -1 := by
  have hrevflow : walkFlow w y x = 1 := by
    rw [walkFlow_skew w y x]
    omega
  have hrev := flow_eq_one_of_walkFlow_eq_one hw hdir hrevflow
  rw [hskew x y, hrev]

/-- Subtracting a directed trail from a unit-capacity flow preserves unit capacity. -/
theorem sub_walkFlow_mem_neg_one_zero_one {u v : V} {w : G.Walk u v}
    (hw : w.IsTrail) {f : V → V → ℤ} (hskew : ∀ x y, f x y = -f y x)
    (hcap : ∀ x y, f x y ∈ ({-1, 0, 1} : Set ℤ))
    (hdir : ∀ a ∈ w.darts, f a.fst a.snd = 1) (x y : V) :
    f x y - walkFlow w x y ∈ ({-1, 0, 1} : Set ℤ) := by
  have hwcap := walkFlow_mem_neg_one_zero_one_of_isTrail hw x y
  have hfvals : f x y = -1 ∨ f x y = 0 ∨ f x y = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcap x y
  have hwvals : walkFlow w x y = -1 ∨ walkFlow w x y = 0 ∨ walkFlow w x y = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hwcap
  rcases hwvals with h | h | h
  · have := flow_eq_neg_one_of_walkFlow_eq_neg_one hw hskew hdir h
    simp [h, this]
  · simpa [h] using hcap x y
  · have := flow_eq_one_of_walkFlow_eq_one hw hdir h
    simp [h, this]

/-- A value-two unit-capacity integral flow decomposes into two edge-disjoint paths. -/
theorem exists_two_edgeDisjoint_paths_of_unitFlow [Fintype V] {u v : V}
    (f : V → V → ℤ)
    (hskew : ∀ x y, f x y = -f y x)
    (hcap : ∀ x y, f x y ∈ ({-1, 0, 1} : Set ℤ))
    (hsupport : ∀ ⦃x y⦄, f x y = 1 → G.Adj x y)
    (hdiv : ∀ x, ∑ y : V, f x y =
      2 * ((if x = u then 1 else 0) - (if x = v then 1 else 0))) :
    ∃ p q : G.Walk u v, p.IsPath ∧ q.IsPath ∧ p.edges.Disjoint q.edges := by
  classical
  have hchain₁ := exists_positive_reflTransGen f hskew hcap (k := 2) (by omega) hdiv
  obtain ⟨w₁, hw₁dir⟩ := exists_walk_of_reflTransGen hsupport hchain₁
  let p : G.Walk u v := w₁.toPath
  have hpPath : p.IsPath := w₁.toPath.2
  have hpTrail : p.IsTrail := hpPath.isTrail
  have hpdir : ∀ a ∈ p.darts, f a.fst a.snd = 1 := by
    intro a ha
    exact hw₁dir a (SimpleGraph.Walk.darts_toPath_subset w₁ ha)
  let f₁ : V → V → ℤ := fun x y ↦ f x y - walkFlow p x y
  have hf₁skew : ∀ x y, f₁ x y = -f₁ y x := by
    intro x y
    simp only [f₁]
    rw [hskew x y, walkFlow_skew p x y]
    omega
  have hf₁cap : ∀ x y, f₁ x y ∈ ({-1, 0, 1} : Set ℤ) := by
    exact fun x y ↦ sub_walkFlow_mem_neg_one_zero_one hpTrail hskew hcap hpdir x y
  have hf₁div : ∀ x, ∑ y : V, f₁ x y =
      (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
    intro x
    change (∑ y : V, (f x y - walkFlow p x y)) = _
    rw [Finset.sum_sub_distrib, hdiv x, sum_walkFlow p x]
    omega
  have hf₁support : ∀ ⦃x y⦄, f₁ x y = 1 → G.Adj x y := by
    intro x y hxy
    have hpvals : walkFlow p x y = -1 ∨ walkFlow p x y = 0 ∨ walkFlow p x y = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
        walkFlow_mem_neg_one_zero_one_of_isTrail hpTrail x y
    rcases hpvals with hpflow | hpflow | hpflow
    · have hf := flow_eq_neg_one_of_walkFlow_eq_neg_one hpTrail hskew hpdir hpflow
      simp [f₁, hf, hpflow] at hxy
    · apply hsupport
      simpa [f₁, hpflow] using hxy
    · have hf := flow_eq_one_of_walkFlow_eq_one hpTrail hpdir hpflow
      simp [f₁, hf, hpflow] at hxy
  have hchain₂ := exists_positive_reflTransGen f₁ hf₁skew hf₁cap (k := 1) (by omega)
    (by
      intro x
      simpa [one_mul] using hf₁div x)
  obtain ⟨w₂, hw₂dir⟩ := exists_walk_of_reflTransGen hf₁support hchain₂
  let q : G.Walk u v := w₂.toPath
  have hqPath : q.IsPath := w₂.toPath.2
  have hqdir : ∀ a ∈ q.darts, f₁ a.fst a.snd = 1 := by
    intro a ha
    exact hw₂dir a (SimpleGraph.Walk.darts_toPath_subset w₂ ha)
  refine ⟨p, q, hpPath, hqPath, List.disjoint_left.mpr ?_⟩
  intro e hep heq
  rw [SimpleGraph.Walk.edges] at hep heq
  rcases List.mem_map.mp hep with ⟨a, ha, hae⟩
  rcases List.mem_map.mp heq with ⟨b, hb, hbe⟩
  have hedge : s(a.fst, a.snd) = s(b.fst, b.snd) := by
    simpa [SimpleGraph.Dart.edge] using hae.trans hbe.symm
  have hpflow : walkFlow p a.fst a.snd = 1 :=
    walkFlow_eq_one_of_mem_darts_of_isTrail hpTrail ha
  have hpvalue : f a.fst a.snd = 1 := hpdir a ha
  rcases Sym2.eq_iff.mp hedge with hsame | hreverse
  · have hqvalue := hqdir b hb
    rw [hsame.1, hsame.2] at hpflow hpvalue
    simp [f₁, hpflow, hpvalue] at hqvalue
  · have hqvalue := hqdir b hb
    have hpflow_rev : walkFlow p a.snd a.fst = -1 := by
      rw [walkFlow_skew p a.snd a.fst, hpflow]
    have hpvalue_rev : f a.snd a.fst = -1 := by
      rw [hskew a.snd a.fst, hpvalue]
    rw [hreverse.1, hreverse.2] at hpflow_rev hpvalue_rev
    simp [f₁, hpflow_rev, hpvalue_rev] at hqvalue

/-- The residual network of a path is reachable when no single edge separates the endpoints. -/
theorem exists_residual_path_of_isEdgeReachable_two [Fintype V] {u v : V}
    (hreach : G.IsEdgeReachable 2 u v)
    (p : G.Walk u v) (hp : p.IsPath) :
    ∃ q : G.Walk u v, q.IsPath ∧
      ∀ a ∈ q.darts, walkFlow p a.fst a.snd ≤ 0 := by
  classical
  let R : V → V → Prop := fun x y ↦ G.Adj x y ∧ walkFlow p x y ≤ 0
  by_contra hno
  have hnochain : ¬Relation.ReflTransGen R u v := by
    intro hchain
    obtain ⟨w, hw⟩ := exists_walk_of_reflTransGen (fun {_ _} h ↦ h.1) hchain
    let q : G.Walk u v := (w.toPath : G.Walk u v)
    have hqdir : ∀ a ∈ q.darts, walkFlow p a.fst a.snd ≤ 0 := by
      intro a ha
      exact (hw a (SimpleGraph.Walk.darts_toPath_subset w ha)).2
    exact hno ⟨q, w.toPath.2, hqdir⟩
  let S : Finset V := Finset.univ.filter fun x ↦ Relation.ReflTransGen R u x
  have huS : u ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, Relation.ReflTransGen.refl⟩
  have hvS : v ∉ S := by simp [S, hnochain]
  have hback : ∀ i, i < p.length → p.getVert (i + 1) ∈ S → p.getVert i ∈ S := by
    intro i hi hnext
    have hadj := p.adj_getVert_succ hi
    let a : G.Dart := ⟨(p.getVert i, p.getVert (i + 1)), hadj⟩
    have ha : a ∈ p.darts := by
      have hiD : i < p.darts.length := by simpa [p.length_darts] using hi
      have hget := p.darts_getElem_eq_getVert i hiD
      have haeq : a = p.darts[i]'hiD := SimpleGraph.Dart.ext _ _ <| by
        change (p.getVert i, p.getVert (i + 1)) = (p.darts[i]'hiD).toProd
        exact congrArg SimpleGraph.Dart.toProd hget.symm
      rw [haeq]
      exact List.getElem_mem hiD
    have hforward : walkFlow p (p.getVert i) (p.getVert (i + 1)) = 1 :=
      walkFlow_eq_one_of_mem_darts_of_isTrail hp.isTrail ha
    have hreverse : walkFlow p (p.getVert (i + 1)) (p.getVert i) = -1 := by
      rw [walkFlow_skew p (p.getVert (i + 1)) (p.getVert i), hforward]
    rw [Finset.mem_filter] at hnext ⊢
    exact ⟨Finset.mem_univ _, Relation.ReflTransGen.tail hnext.2 ⟨hadj.symm, by omega⟩⟩
  have hprefix : ∀ j, j ≤ p.length → p.getVert j ∈ S →
      ∀ i, i ≤ j → p.getVert i ∈ S := by
    intro j
    induction j with
    | zero =>
        intro _hj hjS i hij
        have : i = 0 := by omega
        simpa [this] using hjS
    | succ j ih =>
        intro hjlen hjS i hij
        by_cases hij' : i = j + 1
        · simpa [hij'] using hjS
        · apply ih (by omega) (hback j (by omega) hjS) i (by omega)
  have hexit : ∃ j : ℕ, j ≤ p.length ∧ p.getVert j ∉ S :=
    ⟨p.length, le_rfl, by simpa using hvS⟩
  let k := Nat.find hexit
  have hk : k ≤ p.length ∧ p.getVert k ∉ S := Nat.find_spec hexit
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    exact hk.2 (by simpa [this] using huS)
  let e : Sym2 V := s(p.getVert (k - 1), p.getVert k)
  have hcross_unique : ∀ {x y}, x ∈ S → y ∉ S → G.Adj x y → s(x, y) = e := by
    intro x y hxS hyS hxy
    have hflowpos : 0 < walkFlow p x y := by
      by_contra hnonpos
      apply hyS
      rw [Finset.mem_filter] at hxS ⊢
      exact ⟨Finset.mem_univ y,
        Relation.ReflTransGen.tail hxS.2 ⟨hxy, le_of_not_gt hnonpos⟩⟩
    have hflow : walkFlow p x y = 1 := by
      have hvals : walkFlow p x y = -1 ∨ walkFlow p x y = 0 ∨ walkFlow p x y = 1 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
          walkFlow_mem_neg_one_zero_one_of_isTrail hp.isTrail x y
      rcases hvals with h | h | h <;> omega
    obtain ⟨a, ha, hax, hay⟩ :=
      exists_mem_darts_of_walkFlow_eq_one_of_isTrail hp.isTrail hflow
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
    have hidart := p.darts_getElem_eq_getVert i hi
    have hix : p.getVert i = x := by
      have := congrArg (fun z : G.Dart ↦ z.fst) (hidart.symm.trans hia)
      simpa [hax] using this
    have hiy : p.getVert (i + 1) = y := by
      have := congrArg (fun z : G.Dart ↦ z.snd) (hidart.symm.trans hia)
      simpa [hay] using this
    have hilen : i < p.length := by simpa [p.length_darts] using hi
    have hik : i < k := by
      by_contra hki
      have hk_le_i : k ≤ i := le_of_not_gt hki
      have hkS := hprefix i hilen.le (hix ▸ hxS) k hk_le_i
      exact hk.2 hkS
    have hkle : k ≤ i + 1 := Nat.find_min' hexit ⟨by omega, hiy ▸ hyS⟩
    have hkeq : k = i + 1 := by omega
    simp only [e]
    rw [hkeq]
    simp [hix, hiy]
  have hdeleted : ¬(G.deleteEdges {e}).Reachable u v := by
    rintro ⟨w⟩
    have hexitw : ∃ j : ℕ, j ≤ w.length ∧ w.getVert j ∉ S :=
      ⟨w.length, le_rfl, by simpa using hvS⟩
    let j := Nat.find hexitw
    have hj : j ≤ w.length ∧ w.getVert j ∉ S := Nat.find_spec hexitw
    have hjpos : 0 < j := by
      by_contra hj0
      have : j = 0 := Nat.eq_zero_of_not_pos hj0
      exact hj.2 (by simpa [this] using huS)
    have hprevS : w.getVert (j - 1) ∈ S := by
      by_contra hprev
      exact Nat.find_min hexitw (by omega) ⟨by omega, hprev⟩
    have hadjDel := w.adj_getVert_succ (i := j - 1) (by omega)
    have hadj : G.Adj (w.getVert (j - 1)) (w.getVert j) :=
      by simpa [Nat.sub_add_cancel hjpos] using (SimpleGraph.deleteEdges_adj.mp hadjDel).1
    have hedge := hcross_unique hprevS hj.2 hadj
    exact (SimpleGraph.deleteEdges_adj.mp hadjDel).2
      (by simpa [Nat.sub_add_cancel hjpos] using hedge)
  exact hdeleted (SimpleGraph.isEdgeReachable_two.mp hreach e)

/-- Two-edge reachability produces a value-two flow, hence two edge-disjoint paths. -/
theorem exists_two_edgeDisjoint_paths_of_isEdgeReachable_two [Fintype V] {u v : V}
    (hreach : G.IsEdgeReachable 2 u v) :
    ∃ p q : G.Walk u v, p.IsPath ∧ q.IsPath ∧ p.edges.Disjoint q.edges := by
  classical
  by_cases huv : u = v
  · subst v
    exact ⟨.nil, .nil, by simp, by simp, by simp⟩
  · obtain ⟨w⟩ := hreach.reachable (by omega)
    let p : G.Walk u v := (w.toPath : G.Walk u v)
    have hp : p.IsPath := w.toPath.2
    obtain ⟨q, hq, hqres⟩ := exists_residual_path_of_isEdgeReachable_two hreach p hp
    let f : V → V → ℤ := fun x y ↦ walkFlow p x y + walkFlow q x y
    have hfskew : ∀ x y, f x y = -f y x := by
      intro x y
      simp only [f]
      rw [walkFlow_skew p x y, walkFlow_skew q x y]
      omega
    have hpcap := walkFlow_mem_neg_one_zero_one_of_isTrail hp.isTrail
    have hqcap := walkFlow_mem_neg_one_zero_one_of_isTrail hq.isTrail
    have hfcap : ∀ x y, f x y ∈ ({-1, 0, 1} : Set ℤ) := by
      intro x y
      have hpvals : walkFlow p x y = -1 ∨ walkFlow p x y = 0 ∨ walkFlow p x y = 1 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpcap x y
      have hqvals : walkFlow q x y = -1 ∨ walkFlow q x y = 0 ∨ walkFlow q x y = 1 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hqcap x y
      rcases hqvals with hqflow | hqflow | hqflow
      · have hqrev : walkFlow q y x = 1 := by
          rw [walkFlow_skew q y x, hqflow]
          omega
        have hpresrev : walkFlow p y x ≤ 0 :=
          property_of_walkFlow_eq_one hq.isTrail (fun a b ↦ walkFlow p a b ≤ 0) hqres hqrev
        have hpres : 0 ≤ walkFlow p x y := by
          rw [walkFlow_skew p y x] at hpresrev
          omega
        rcases hpvals with h | h | h
        · omega
        · simp [f, h, hqflow]
        · simp [f, h, hqflow]
      · rcases hpvals with h | h | h <;> simp [f, h, hqflow]
      · have hpres : walkFlow p x y ≤ 0 :=
          property_of_walkFlow_eq_one hq.isTrail (fun a b ↦ walkFlow p a b ≤ 0) hqres hqflow
        rcases hpvals with h | h | h
        · simp [f, h, hqflow]
        · simp [f, h, hqflow]
        · omega
    have hfsupport : ∀ ⦃x y⦄, f x y = 1 → G.Adj x y := by
      intro x y hfxy
      have hpvals : walkFlow p x y = -1 ∨ walkFlow p x y = 0 ∨ walkFlow p x y = 1 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpcap x y
      have hqvals : walkFlow q x y = -1 ∨ walkFlow q x y = 0 ∨ walkFlow q x y = 1 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hqcap x y
      rcases hpvals with hpflow | hpflow | hpflow <;>
        rcases hqvals with hqflow | hqflow | hqflow
      all_goals try {simp [f, hpflow, hqflow] at hfxy}
      · exact property_of_walkFlow_eq_one hq.isTrail G.Adj
          (fun a _ha ↦ a.adj) hqflow
      · exact property_of_walkFlow_eq_one hp.isTrail G.Adj
          (fun a _ha ↦ a.adj) hpflow
    have hfdiv : ∀ x, ∑ y : V, f x y =
        2 * ((if x = u then 1 else 0) - (if x = v then 1 else 0)) := by
      intro x
      change (∑ y : V, (walkFlow p x y + walkFlow q x y)) = _
      rw [Finset.sum_add_distrib, sum_walkFlow p x, sum_walkFlow q x]
      omega
    exact exists_two_edgeDisjoint_paths_of_unitFlow f hfskew hfcap hfsupport hfdiv

/-- **Finite two-edge Menger theorem.** Two vertices of a finite simple graph remain connected
after deletion of any one edge iff two edge-disjoint paths join them. -/
theorem isEdgeReachable_two_iff_exists_edgeDisjoint_paths [Fintype V] {u v : V} :
    G.IsEdgeReachable 2 u v ↔
      ∃ p q : G.Walk u v, p.IsPath ∧ q.IsPath ∧ p.edges.Disjoint q.edges := by
  constructor
  · exact exists_two_edgeDisjoint_paths_of_isEdgeReachable_two
  · rintro ⟨p, q, _hp, _hq, hpq⟩
    rw [SimpleGraph.isEdgeReachable_two]
    intro e
    by_cases hep : e ∈ p.edges
    · have heq : e ∉ q.edges := fun heq ↦ List.disjoint_left.mp hpq hep heq
      exact ⟨q.toDeleteEdges {e} (fun e' he' ↦ by
        simpa only [Set.mem_singleton_iff, ne_eq] using
          (fun h : e' = e ↦ heq (h ▸ he')))⟩
    · exact ⟨p.toDeleteEdges {e} (fun e' he' ↦ by
        simpa only [Set.mem_singleton_iff, ne_eq] using
          (fun h : e' = e ↦ hep (h ▸ he')))⟩

/-- A deletion criterion useful for exploration arguments. Two proposed walks suffice unless
the deleted edge lies on both; in that overlap case an edge-dependent avoiding walk may be
supplied. -/
theorem isEdgeReachable_two_of_walks_and_overlap_avoidance {u v : V}
    (p q : G.Walk u v)
    (havoid : ∀ e, e ∈ p.edges → e ∈ q.edges → ∃ r : G.Walk u v, e ∉ r.edges) :
    G.IsEdgeReachable 2 u v := by
  rw [SimpleGraph.isEdgeReachable_two]
  intro e
  by_cases hep : e ∈ p.edges
  · by_cases heq : e ∈ q.edges
    · obtain ⟨r, her⟩ := havoid e hep heq
      exact ⟨r.toDeleteEdges {e} (fun e' he' ↦ by
        simpa only [Set.mem_singleton_iff, ne_eq] using
          (fun h : e' = e ↦ her (h ▸ he')))⟩
    · exact ⟨q.toDeleteEdges {e} (fun e' he' ↦ by
        simpa only [Set.mem_singleton_iff, ne_eq] using
          (fun h : e' = e ↦ heq (h ▸ he')))⟩
  · exact ⟨p.toDeleteEdges {e} (fun e' he' ↦ by
      simpa only [Set.mem_singleton_iff, ne_eq] using
        (fun h : e' = e ↦ hep (h ▸ he')))⟩

end TwoEdgeMenger

end Percolation
