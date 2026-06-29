import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Range

/-!
# Cubic lattice graph vocabulary

This file starts the production Mathlib-native encoding for Grimmett's cubic lattice `L^d`.
The current API is intentionally small: it gives the vertex type, nearest-neighbour graph,
fixed edge type, edge configurations, open walks, and self-avoiding-walk counts needed by the
first critical-probability target.
-/

namespace Percolation

/-- Vertices of the `d`-dimensional cubic lattice. -/
abbrev Cubic (d : ℕ) := Fin d → ℤ

/-- The origin of the cubic lattice. -/
def cubicOrigin {d : ℕ} : Cubic d := fun _ ↦ 0

/-- A positively oriented unit step in the cubic lattice. The undirected graph is obtained by
symmetrizing this relation with `SimpleGraph.fromRel`. -/
def cubicStep (d : ℕ) (x y : Cubic d) : Prop :=
  ∃ i : Fin d, y = Function.update x i (x i + 1)

/-- The nearest-neighbour graph on the cubic lattice. -/
def cubicGraph (d : ℕ) : SimpleGraph (Cubic d) :=
  SimpleGraph.fromRel (cubicStep d)

/-- One of the `2d` signed coordinate directions in the cubic lattice. The boolean is `true`
for the positive direction and `false` for the negative direction. -/
abbrev CubicDirection (d : ℕ) := Fin d × Bool

/-- The signed coordinate increment attached to a cubic-lattice direction. -/
def cubicDirectionIncrement {d : ℕ} (a : CubicDirection d) : ℤ :=
  if a.2 then 1 else -1

/-- Move one lattice step from `x` in the signed coordinate direction `a`. -/
def cubicStepFrom {d : ℕ} (x : Cubic d) (a : CubicDirection d) : Cubic d :=
  Function.update x a.1 (x a.1 + cubicDirectionIncrement a)

/-- A negative step followed by the corresponding positive step returns to the starting vertex. -/
theorem cubicStepFrom_neg_pos {d : ℕ} (x : Cubic d) (i : Fin d) :
    cubicStepFrom (cubicStepFrom x (i, false)) (i, true) = x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [cubicStepFrom, cubicDirectionIncrement]
  · simp [cubicStepFrom, cubicDirectionIncrement, hji]

/-- A positive step followed by the corresponding negative step returns to the starting vertex. -/
theorem cubicStepFrom_pos_neg {d : ℕ} (x : Cubic d) (i : Fin d) :
    cubicStepFrom (cubicStepFrom x (i, true)) (i, false) = x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [cubicStepFrom, cubicDirectionIncrement]
  · simp [cubicStepFrom, cubicDirectionIncrement, hji]

/-- Translate a cubic-lattice vertex so that `x` is sent to `y`. -/
def cubicTranslate {d : ℕ} (x y z : Cubic d) : Cubic d :=
  fun i ↦ z i + (y i - x i)

@[simp]
theorem cubicTranslate_self {d : ℕ} (x y : Cubic d) : cubicTranslate x y x = y := by
  ext i
  simp [cubicTranslate]

/-- Translating every lattice vertex by a fixed offset is injective. -/
theorem cubicTranslate_injective {d : ℕ} (x y : Cubic d) :
    Function.Injective (cubicTranslate x y) := by
  intro z z' h
  ext i
  have hi := congrFun h i
  dsimp [cubicTranslate] at hi
  omega

/-- Taking the same signed coordinate step from two translated starts preserves the translation
offset. -/
theorem cubicTranslate_stepFrom {d : ℕ} (x y : Cubic d) (a : CubicDirection d) (z : Cubic d) :
    cubicTranslate (cubicStepFrom x a) (cubicStepFrom y a) z = cubicTranslate x y z := by
  rcases a with ⟨i, b⟩
  ext j
  by_cases hji : j = i
  · subst hji
    simp [cubicTranslate, cubicStepFrom, cubicDirectionIncrement]
  · simp [cubicTranslate, cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji]

/-- The positive signed directions are exactly the oriented steps used to build `cubicGraph`. -/
theorem cubicStep_pos {d : ℕ} (x : Cubic d) (i : Fin d) :
    cubicStep d x (cubicStepFrom x (i, true)) := by
  exact ⟨i, by simp [cubicStepFrom, cubicDirectionIncrement]⟩

/-- Moving in any signed coordinate direction gives an adjacent vertex in the undirected cubic
lattice graph. -/
theorem cubicGraph_adj_stepFrom {d : ℕ} (x : Cubic d) (a : CubicDirection d) :
    (cubicGraph d).Adj x (cubicStepFrom x a) := by
  classical
  rcases a with ⟨i, b⟩
  by_cases hb : b
  · subst hb
    rw [cubicGraph, SimpleGraph.fromRel_adj]
    exact ⟨by
      intro h
      have hcoord := congr_fun h i
      simp [cubicStepFrom, cubicDirectionIncrement] at hcoord, Or.inl (cubicStep_pos x i)⟩
  · rw [Bool.eq_false_of_not_eq_true hb]
    rw [cubicGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inr ?_⟩
    · intro h
      have hcoord := congr_fun h i
      simp [cubicStepFrom, cubicDirectionIncrement] at hcoord
    · refine ⟨i, ?_⟩
      ext j
      by_cases hji : j = i
      · subst hji
        simp [cubicStepFrom, cubicDirectionIncrement]
      · simp [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji]

/-- Adjacency in the cubic graph is exactly moving by one signed coordinate step. -/
theorem cubicGraph_adj_iff_exists_stepFrom {d : ℕ} (x y : Cubic d) :
    (cubicGraph d).Adj x y ↔ ∃ a : CubicDirection d, y = cubicStepFrom x a := by
  classical
  constructor
  · intro h
    rw [cubicGraph, SimpleGraph.fromRel_adj] at h
    rcases h with ⟨_hne, hstep | hstep⟩
    · rcases hstep with ⟨i, rfl⟩
      exact ⟨(i, true), by simp [cubicStepFrom, cubicDirectionIncrement]⟩
    · rcases hstep with ⟨i, hxy⟩
      refine ⟨(i, false), ?_⟩
      ext j
      by_cases hji : j = i
      · subst j
        have hcoord := congr_fun hxy i
        simp [cubicStepFrom, cubicDirectionIncrement] at hcoord ⊢
        omega
      · have hcoord := congr_fun hxy j
        simp [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji] at hcoord ⊢
        exact hcoord.symm
  · rintro ⟨a, rfl⟩
    exact cubicGraph_adj_stepFrom x a

/-- A single cubic step changes any fixed coordinate by at most one in the positive direction. -/
theorem cubicStepFrom_coord_le_add_one {d : ℕ} (x : Cubic d) (a : CubicDirection d)
    (i : Fin d) :
    cubicStepFrom x a i ≤ x i + 1 := by
  rcases a with ⟨j, b⟩
  by_cases hji : i = j
  · subst i
    by_cases hb : b
    · simp [cubicStepFrom, cubicDirectionIncrement, hb]
    · simp [cubicStepFrom, cubicDirectionIncrement, hb]
  · simp [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji]

/-- A single cubic step changes any fixed coordinate by at most one in the negative direction. -/
theorem cubicStepFrom_coord_sub_one_le {d : ℕ} (x : Cubic d) (a : CubicDirection d)
    (i : Fin d) :
    x i ≤ cubicStepFrom x a i + 1 := by
  rcases a with ⟨j, b⟩
  by_cases hji : i = j
  · subst i
    by_cases hb : b
    · simp [cubicStepFrom, cubicDirectionIncrement, hb]
      omega
    · simp [cubicStepFrom, cubicDirectionIncrement, hb]
  · simp [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji]

/-- Along a cubic walk, a coordinate can increase by at most the walk length. -/
theorem cubicWalk_coord_le_start_add_length {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (i : Fin d) :
    v i ≤ u i + (w.length : ℤ) := by
  induction w with
  | nil =>
      simp
  | @cons u₀ v₀ w₀ h p ih =>
      rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp h with ⟨a, ha⟩
      have ih' : w₀ i ≤ (cubicStepFrom u₀ a) i + (p.length : ℤ) := by
        simpa [ha] using ih
      have hstep := cubicStepFrom_coord_le_add_one u₀ a i
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- Along a cubic walk, a coordinate can decrease by at most the walk length. -/
theorem cubicWalk_start_coord_le_end_add_length {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (i : Fin d) :
    u i ≤ v i + (w.length : ℤ) := by
  induction w with
  | nil =>
      simp
  | @cons u₀ v₀ w₀ h p ih =>
      rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp h with ⟨a, ha⟩
      have ih' : (cubicStepFrom u₀ a) i ≤ w₀ i + (p.length : ℤ) := by
        simpa [ha] using ih
      have hstep := cubicStepFrom_coord_sub_one_le u₀ a i
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- Embed the first `m` coordinates of the cubic lattice into `d` dimensions, filling all other
coordinates with zero. The dimension hypothesis is carried by the lemmas below. -/
def cubicEmbed (m d : ℕ) (x : Cubic m) : Cubic d :=
  fun j ↦ if hj : (j : ℕ) < m then x ⟨j, hj⟩ else 0

@[simp]
theorem cubicEmbed_castLE {m d : ℕ} (hmd : m ≤ d) (x : Cubic m) (i : Fin m) :
    cubicEmbed m d x (Fin.castLE hmd i) = x i := by
  simp [cubicEmbed]

@[simp]
theorem cubicEmbed_origin (m d : ℕ) :
    cubicEmbed m d (cubicOrigin : Cubic m) = (cubicOrigin : Cubic d) := by
  ext j
  by_cases hj : (j : ℕ) < m <;> simp [cubicEmbed, cubicOrigin, hj]

/-- The coordinate embedding is injective when the source dimension is at most the target
dimension. -/
theorem cubicEmbed_injective {m d : ℕ} (hmd : m ≤ d) :
    Function.Injective (cubicEmbed m d : Cubic m → Cubic d) := by
  intro x y hxy
  ext i
  have hcoord := congrFun hxy (Fin.castLE hmd i)
  simpa [cubicEmbed] using hcoord

/-- Coordinate embedding commutes with a signed step in the source lattice. -/
theorem cubicEmbed_stepFrom {m d : ℕ} (hmd : m ≤ d) (x : Cubic m)
    (a : CubicDirection m) :
    cubicEmbed m d (cubicStepFrom x a) =
      cubicStepFrom (cubicEmbed m d x) (Fin.castLE hmd a.1, a.2) := by
  ext j
  by_cases hj : (j : ℕ) < m
  · let i : Fin m := ⟨j, hj⟩
    by_cases hi : i = a.1
    · have hjcast : j = Fin.castLE hmd a.1 := by
        ext
        change (i : ℕ) = (a.1 : ℕ)
        exact congrArg Fin.val hi
      subst hjcast
      simp [cubicEmbed, cubicStepFrom, cubicDirectionIncrement]
    · have hjcast : j ≠ Fin.castLE hmd a.1 := by
        intro h
        apply hi
        ext
        change (j : ℕ) = (a.1 : ℕ)
        simpa using congrArg Fin.val h
      simp [cubicEmbed, cubicStepFrom, cubicDirectionIncrement, hj, i, hi, hjcast]
  · have hne : j ≠ Fin.castLE hmd a.1 := by
      intro h
      apply hj
      rw [h]
      exact a.1.2
    simp [cubicEmbed, cubicStepFrom, hj, hne]

/-- Coordinate embedding preserves cubic-lattice adjacency. -/
theorem cubicEmbed_adj {m d : ℕ} (hmd : m ≤ d) {x y : Cubic m}
    (hxy : (cubicGraph m).Adj x y) :
    (cubicGraph d).Adj (cubicEmbed m d x) (cubicEmbed m d y) := by
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨a, rfl⟩
  rw [cubicEmbed_stepFrom hmd]
  exact cubicGraph_adj_stepFrom _ _

/-- The graph homomorphism induced by the coordinate embedding of cubic lattices. -/
def cubicEmbedHom {m d : ℕ} (hmd : m ≤ d) :
    (cubicGraph m) →g (cubicGraph d) where
  toFun := cubicEmbed m d
  map_rel' := fun hxy ↦ cubicEmbed_adj hmd hxy

@[simp]
theorem cubicEmbedHom_apply {m d : ℕ} (hmd : m ≤ d) (x : Cubic m) :
    cubicEmbedHom hmd x = cubicEmbed m d x := rfl

/-- The fixed edge type of the cubic lattice graph. -/
abbrev CubicEdge (d : ℕ) := {e : Sym2 (Cubic d) // e ∈ (cubicGraph d).edgeSet}

/-- The edge embedding induced by the coordinate embedding of cubic lattices. -/
def cubicEdgeEmbed {m d : ℕ} (hmd : m ≤ d) : CubicEdge m ↪ CubicEdge d where
  toFun := (cubicEmbedHom hmd).mapEdgeSet
  inj' := by
    simpa [cubicEmbedHom] using
      (SimpleGraph.Hom.mapEdgeSet.injective (cubicEmbedHom hmd) (cubicEmbed_injective hmd))

/-- A bond configuration is a set of open lattice edges. -/
abbrev EdgeConfiguration (d : ℕ) := Set (CubicEdge d)

/-- Pull a bond configuration on the target cubic lattice back to an embedded lower-dimensional
lattice. This is the deterministic part of the dimension-monotonicity coupling. -/
def cubicConfigurationPullback {m d : ℕ} (hmd : m ≤ d)
    (ω : EdgeConfiguration d) : EdgeConfiguration m :=
  {e | cubicEdgeEmbed hmd e ∈ ω}

/-- An edge is open in a configuration. -/
def edgeOpen {d : ℕ} (ω : EdgeConfiguration d) (e : CubicEdge d) : Prop :=
  e ∈ ω

/-- Every edge traversed by a walk is open in the configuration. -/
def walkIsOpen {d : ℕ} (ω : EdgeConfiguration d) {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) : Prop :=
  ∀ e, ∀ he : e ∈ w.edges, edgeOpen ω ⟨e, w.edges_subset_edgeSet he⟩

/-- Copying a walk across endpoint equalities does not change its open-edge event. -/
theorem walkIsOpen_copy {d : ℕ} {ω : EdgeConfiguration d} {u v u' v' : Cubic d}
    (w : (cubicGraph d).Walk u v) (hu : u = u') (hv : v = v') :
    walkIsOpen ω (w.copy hu hv) ↔ walkIsOpen ω w := by
  constructor
  · intro h e he
    exact h e (by simpa [SimpleGraph.Walk.edges_copy] using he)
  · intro h e he
    exact h e (by simpa [SimpleGraph.Walk.edges_copy] using he)

/-- An open walk in a pulled-back lower-dimensional configuration maps to an open walk in the
ambient configuration. -/
theorem walkIsOpen_map_cubicEmbedHom {m d : ℕ} (hmd : m ≤ d)
    {ω : EdgeConfiguration d} {u v : Cubic m} (w : (cubicGraph m).Walk u v)
    (hopen : walkIsOpen (cubicConfigurationPullback hmd ω) w) :
    walkIsOpen ω (w.map (cubicEmbedHom hmd)) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  rcases List.mem_map.mp he with ⟨e₀, he₀, rfl⟩
  have hdown := hopen e₀ he₀
  change cubicEdgeEmbed hmd ⟨e₀, w.edges_subset_edgeSet he₀⟩ ∈ ω at hdown
  simpa [edgeOpen, cubicEdgeEmbed, SimpleGraph.Hom.mapEdgeSet] using hdown

/-- Openness is inherited by a walk whose traversed edge list is contained in an open walk's edge
list. -/
theorem walkIsOpen_of_edges_subset {d : ℕ} {ω : EdgeConfiguration d}
    {u v u' v' : Cubic d} {p : (cubicGraph d).Walk u v}
    {q : (cubicGraph d).Walk u' v'} (hopen : walkIsOpen ω q)
    (hsub : p.edges ⊆ q.edges) :
    walkIsOpen ω p := by
  intro e he
  exact hopen e (hsub he)

/-- A contiguous subwalk of a path is again a path. -/
theorem walk_isPath_of_isSubwalk {V : Type*} {G : SimpleGraph V} {u v u' v' : V}
    {p : G.Walk u v} {q : G.Walk u' v'} (hp : p.IsPath) (hsub : q.IsSubwalk p) :
    q.IsPath := by
  rw [SimpleGraph.Walk.isPath_def] at hp ⊢
  exact (SimpleGraph.Walk.isSubwalk_iff_support_isInfix.mp hsub).nodup hp

/-- Openness is inherited by a contiguous subwalk. -/
theorem walkIsOpen_of_isSubwalk {d : ℕ} {ω : EdgeConfiguration d} {u v u' v' : Cubic d}
    {p : (cubicGraph d).Walk u v} {q : (cubicGraph d).Walk u' v'}
    (hopen : walkIsOpen ω p) (hsub : q.IsSubwalk p) :
    walkIsOpen ω q :=
  walkIsOpen_of_edges_subset hopen hsub.edges_subset

/-- Last-visit suffix for a walk and a region predicate. If a walk visits a region but ends
outside it, then some suffix starts at a region vertex and all later vertices of the suffix are
outside the region. This is the finite combinatorial core of the box-exit step in Peierls'
argument. -/
theorem exists_isSubwalk_suffix_from_last_region {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    {u v : V} (w : G.Walk u v) (hmem : ∃ x : V, x ∈ w.support ∧ P x)
    (hend : ¬ P v) :
    ∃ x : V, P x ∧ ∃ q : G.Walk x v,
      q.IsSubwalk w ∧ ∀ z : V, z ∈ q.support.tail → ¬ P z := by
  induction w with
  | nil =>
      rcases hmem with ⟨x, hx, hxP⟩
      rw [SimpleGraph.Walk.mem_support_nil_iff] at hx
      subst x
      exact (hend hxP).elim
  | cons h p ih =>
      by_cases htail : ∃ x : V, x ∈ p.support ∧ P x
      · rcases ih htail hend with ⟨x, hxP, q, hqsub, hqoutside⟩
        exact ⟨x, hxP, q, hqsub.trans (SimpleGraph.Walk.isSubwalk_cons p h), hqoutside⟩
      · rcases hmem with ⟨x, hx, hxP⟩
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with hx | hx
        · subst x
          refine ⟨_, hxP, SimpleGraph.Walk.cons h p, SimpleGraph.Walk.isSubwalk_rfl _, ?_⟩
          intro z hz
          exact fun hzP ↦ htail ⟨z, by simpa using hz, hzP⟩
        · exact (htail ⟨x, hx, hxP⟩).elim

/-- Openness is preserved by concatenating open walks. -/
theorem walkIsOpen_append {d : ℕ} {ω : EdgeConfiguration d} {u v w : Cubic d}
    {p : (cubicGraph d).Walk u v} {q : (cubicGraph d).Walk v w}
    (hp : walkIsOpen ω p) (hq : walkIsOpen ω q) :
    walkIsOpen ω (p.append q) := by
  intro e he
  rw [SimpleGraph.Walk.edges_append] at he
  rcases List.mem_append.mp he with he | he
  · exact hp e he
  · exact hq e he

/-- Reversing a walk preserves its open-edge event. -/
theorem walkIsOpen_reverse {d : ℕ} {ω : EdgeConfiguration d} {u v : Cubic d}
    {w : (cubicGraph d).Walk u v} (hopen : walkIsOpen ω w) :
    walkIsOpen ω w.reverse := by
  intro e he
  rw [SimpleGraph.Walk.edges_reverse] at he
  exact hopen e (List.mem_reverse.mp he)

/-- Openness is inherited by a terminal segment of a walk. -/
theorem walkIsOpen_drop {d : ℕ} {ω : EdgeConfiguration d} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w) (n : ℕ) :
    walkIsOpen ω (w.drop n) :=
  walkIsOpen_of_edges_subset hopen ((SimpleGraph.Walk.isSubwalk_drop w n).edges_subset)

/-- Bypassing repeated vertices preserves openness because the bypassed walk uses a sublist of the
original walk's edges. -/
theorem walkIsOpen_bypass {d : ℕ} {ω : EdgeConfiguration d} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w) :
    walkIsOpen ω w.bypass :=
  walkIsOpen_of_edges_subset hopen (SimpleGraph.Walk.edges_bypass_subset w)

/-- The self-avoiding path extracted from an open walk is open. -/
theorem walkIsOpen_toPath {d : ℕ} {ω : EdgeConfiguration d} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w) :
    walkIsOpen ω (w.toPath : (cubicGraph d).Walk u v) :=
  walkIsOpen_of_edges_subset hopen (SimpleGraph.Walk.edges_toPath_subset w)

/-- Two paths concatenate to a path when the first path's support is disjoint from the tail
support of the second path. The shared endpoint is the head of the second support, so it is not in
`q.support.tail`. -/
theorem walk_isPath_append_of_disjoint_tail {d : ℕ} {u v w : Cubic d}
    {p : (cubicGraph d).Walk u v} {q : (cubicGraph d).Walk v w}
    (hp : p.IsPath) (hq : q.IsPath) (hdisj : p.support.Disjoint q.support.tail) :
    (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
  exact hp.support_nodup.append hq.support_nodup.tail hdisj

/-- To show an appended walk stays in a region, it is enough to show each factor stays there. -/
theorem walk_append_support_subset {d : ℕ} {u v w : Cubic d}
    {p : (cubicGraph d).Walk u v} {q : (cubicGraph d).Walk v w}
    {P : Cubic d → Prop}
    (hp : ∀ z : Cubic d, z ∈ p.support → P z)
    (hq : ∀ z : Cubic d, z ∈ q.support → P z) :
    ∀ z : Cubic d, z ∈ (p.append q).support → P z := by
  intro z hz
  rw [SimpleGraph.Walk.support_append] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp z hz
  · exact hq z (List.mem_of_mem_tail hz)

/-- The list of lattice edges traversed by a graph walk, with membership in the cubic edge set
recorded in the subtype. -/
noncomputable def walkEdgeList {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) : List (CubicEdge d) :=
  w.edges.attach.map fun e ↦ ⟨e.1, w.edges_subset_edgeSet e.2⟩

/-- The finite set of lattice edges traversed by a graph walk. -/
noncomputable def walkEdgeFinset {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) : Finset (CubicEdge d) :=
  (walkEdgeList w).toFinset

@[simp]
theorem mem_walkEdgeFinset_iff {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (e : CubicEdge d) :
    e ∈ walkEdgeFinset w ↔ (e : Sym2 (Cubic d)) ∈ w.edges := by
  classical
  constructor
  · intro he
    rw [walkEdgeFinset, List.mem_toFinset] at he
    rcases List.mem_map.mp he with ⟨a, _ha, hae⟩
    have hval : a.1 = (e : Sym2 (Cubic d)) :=
      congrArg (fun e : CubicEdge d ↦ (e : Sym2 (Cubic d))) hae
    exact hval ▸ a.2
  · intro he
    rw [walkEdgeFinset, List.mem_toFinset]
    exact List.mem_map.mpr ⟨⟨e, he⟩, List.mem_attach _ _, Subtype.ext rfl⟩

/-- A trail has no repeated traversed lattice edges. -/
theorem nodup_walkEdgeList_of_isTrail {d : ℕ} {u v : Cubic d}
    {w : (cubicGraph d).Walk u v} (h : w.IsTrail) :
    (walkEdgeList w).Nodup := by
  classical
  unfold walkEdgeList
  exact h.edges_nodup.attach.map (by
    intro a b hab
    exact Subtype.ext (congrArg (fun e : CubicEdge d ↦ (e : Sym2 (Cubic d))) hab))

/-- For a trail, the number of distinct traversed lattice edges is its length. -/
theorem walkEdgeFinset_card_of_isTrail {d : ℕ} {u v : Cubic d}
    {w : (cubicGraph d).Walk u v} (h : w.IsTrail) :
    (walkEdgeFinset w).card = w.length := by
  classical
  rw [walkEdgeFinset, List.toFinset_card_of_nodup (nodup_walkEdgeList_of_isTrail h)]
  simp [walkEdgeList, SimpleGraph.Walk.length_edges]

/-- There is an open self-avoiding walk of length at least `n` from the origin. -/
def hasOpenPathOfLengthAtLeast (d : ℕ) (ω : EdgeConfiguration d) (n : ℕ) : Prop :=
  ∃ v : Cubic d, ∃ w : (cubicGraph d).Walk cubicOrigin v,
    w.IsPath ∧ n ≤ w.length ∧ walkIsOpen ω w

/-- There is an open self-avoiding walk of length at least `n` from a prescribed lattice
vertex. This is the vertex-rooted form used by the planar separation step in Grimmett's Peierls
argument. -/
def hasOpenPathOfLengthAtLeastFrom (d : ℕ) (ω : EdgeConfiguration d)
    (x : Cubic d) (n : ℕ) : Prop :=
  ∃ v : Cubic d, ∃ w : (cubicGraph d).Walk x v,
    w.IsPath ∧ n ≤ w.length ∧ walkIsOpen ω w

/-- There is an open self-avoiding walk of length exactly `n` from the origin. -/
def hasOpenPathOfLengthExactly (d : ℕ) (ω : EdgeConfiguration d) (n : ℕ) : Prop :=
  ∃ v : Cubic d, ∃ w : (cubicGraph d).Walk cubicOrigin v,
    w.IsPath ∧ w.length = n ∧ walkIsOpen ω w

/-- There is an open self-avoiding walk of length exactly `n` from a prescribed lattice
vertex. -/
def hasOpenPathOfLengthExactlyFrom (d : ℕ) (ω : EdgeConfiguration d)
    (x : Cubic d) (n : ℕ) : Prop :=
  ∃ v : Cubic d, ∃ w : (cubicGraph d).Walk x v,
    w.IsPath ∧ w.length = n ∧ walkIsOpen ω w

@[simp]
theorem hasOpenPathOfLengthAtLeastFrom_origin {d : ℕ} {ω : EdgeConfiguration d} {n : ℕ} :
    hasOpenPathOfLengthAtLeastFrom d ω cubicOrigin n ↔
      hasOpenPathOfLengthAtLeast d ω n :=
  Iff.rfl

@[simp]
theorem hasOpenPathOfLengthExactlyFrom_origin {d : ℕ} {ω : EdgeConfiguration d} {n : ℕ} :
    hasOpenPathOfLengthExactlyFrom d ω cubicOrigin n ↔
      hasOpenPathOfLengthExactly d ω n :=
  Iff.rfl

/-- Source-to-endpoint form of open path concatenation: a finite open connector and a disjoint
open path after it produce an open self-avoiding path from the connector's start. -/
theorem hasOpenPathOfLengthAtLeastFrom_of_append_disjoint_tail {d n : ℕ}
    {ω : EdgeConfiguration d} {u v w : Cubic d}
    {p : (cubicGraph d).Walk u v} {q : (cubicGraph d).Walk v w}
    (hp : p.IsPath) (hq : q.IsPath) (hdisj : p.support.Disjoint q.support.tail)
    (hlen : n ≤ (p.append q).length) (hpopen : walkIsOpen ω p)
    (hqopen : walkIsOpen ω q) :
    hasOpenPathOfLengthAtLeastFrom d ω u n :=
  ⟨w, p.append q, walk_isPath_append_of_disjoint_tail hp hq hdisj, hlen,
    walkIsOpen_append hpopen hqopen⟩

/-- Openness is inherited by an initial segment of a walk. -/
theorem walkIsOpen_take {d : ℕ} {ω : EdgeConfiguration d} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w) (n : ℕ) :
    walkIsOpen ω (w.take n) := by
  intro e he
  exact hopen e ((SimpleGraph.Walk.isSubwalk_take w n).edges_subset he)

/-- An open self-avoiding path of length at least `n` contains an open initial path of exactly
length `n`. -/
theorem hasOpenPathOfLengthAtLeast_imp_hasOpenPathOfLengthExactly {d n : ℕ}
    {ω : EdgeConfiguration d} :
    hasOpenPathOfLengthAtLeast d ω n → hasOpenPathOfLengthExactly d ω n := by
  rintro ⟨v, w, hwpath, hlen, hopen⟩
  refine ⟨w.getVert n, w.take n, hwpath.take n, ?_, walkIsOpen_take w hopen n⟩
  simp [Nat.min_eq_left hlen]

/-- An open self-avoiding path from a prescribed vertex of length at least `n` contains an open
initial path from that vertex of exactly length `n`. -/
theorem hasOpenPathOfLengthAtLeastFrom_imp_hasOpenPathOfLengthExactlyFrom
    {d n : ℕ} {ω : EdgeConfiguration d} {x : Cubic d} :
    hasOpenPathOfLengthAtLeastFrom d ω x n →
      hasOpenPathOfLengthExactlyFrom d ω x n := by
  rintro ⟨v, w, hwpath, hlen, hopen⟩
  refine ⟨w.getVert n, w.take n, hwpath.take n, ?_, walkIsOpen_take w hopen n⟩
  simp [Nat.min_eq_left hlen]

/-- An open self-avoiding path of exact length `n` is, in particular, one of length at least
`n`. -/
theorem hasOpenPathOfLengthExactly_imp_hasOpenPathOfLengthAtLeast {d n : ℕ}
    {ω : EdgeConfiguration d} :
    hasOpenPathOfLengthExactly d ω n → hasOpenPathOfLengthAtLeast d ω n := by
  rintro ⟨v, w, hwpath, hwlen, hopen⟩
  exact ⟨v, w, hwpath, by simp [hwlen], hopen⟩

/-- An open self-avoiding path of exact length `n` from a prescribed vertex is, in particular,
one of length at least `n`. -/
theorem hasOpenPathOfLengthExactlyFrom_imp_hasOpenPathOfLengthAtLeastFrom
    {d n : ℕ} {ω : EdgeConfiguration d} {x : Cubic d} :
    hasOpenPathOfLengthExactlyFrom d ω x n →
      hasOpenPathOfLengthAtLeastFrom d ω x n := by
  rintro ⟨v, w, hwpath, hwlen, hopen⟩
  exact ⟨v, w, hwpath, by simp [hwlen], hopen⟩

/-- The “at least `n`” and “exactly `n`” formulations of finite open self-avoiding paths are
equivalent for paths from the origin. -/
theorem hasOpenPathOfLengthAtLeast_iff_hasOpenPathOfLengthExactly {d n : ℕ}
    {ω : EdgeConfiguration d} :
    hasOpenPathOfLengthAtLeast d ω n ↔ hasOpenPathOfLengthExactly d ω n :=
  ⟨hasOpenPathOfLengthAtLeast_imp_hasOpenPathOfLengthExactly,
    hasOpenPathOfLengthExactly_imp_hasOpenPathOfLengthAtLeast⟩

/-- The “at least `n`” and “exactly `n`” formulations of finite open self-avoiding paths are
equivalent from any prescribed starting vertex. -/
theorem hasOpenPathOfLengthAtLeastFrom_iff_hasOpenPathOfLengthExactlyFrom
    {d n : ℕ} {ω : EdgeConfiguration d} {x : Cubic d} :
    hasOpenPathOfLengthAtLeastFrom d ω x n ↔
      hasOpenPathOfLengthExactlyFrom d ω x n :=
  ⟨hasOpenPathOfLengthAtLeastFrom_imp_hasOpenPathOfLengthExactlyFrom,
    hasOpenPathOfLengthExactlyFrom_imp_hasOpenPathOfLengthAtLeastFrom⟩

/-- A lower-dimensional open path in a pulled-back configuration gives an embedded open path of
the same length in the ambient configuration. -/
theorem hasOpenPathOfLengthAtLeast_cubicConfigurationPullback {m d n : ℕ}
    (hmd : m ≤ d) {ω : EdgeConfiguration d} :
    hasOpenPathOfLengthAtLeast m (cubicConfigurationPullback hmd ω) n →
      hasOpenPathOfLengthAtLeast d ω n := by
  rintro ⟨v, w, hwpath, hlen, hopen⟩
  let wmap : (cubicGraph d).Walk cubicOrigin (cubicEmbed m d v) :=
    (w.map (cubicEmbedHom hmd)).copy (by simp) (by simp)
  refine ⟨cubicEmbed m d v, wmap, ?_, ?_, ?_⟩
  · dsimp [wmap]
    rw [SimpleGraph.Walk.isPath_copy]
    exact SimpleGraph.Walk.map_isPath_of_injective
      (by simpa [cubicEmbedHom] using cubicEmbed_injective hmd) hwpath
  · dsimp [wmap]
    rw [SimpleGraph.Walk.length_copy]
    change n ≤ (w.map (cubicEmbedHom hmd)).length
    rw [w.length_map]
    exact hlen
  · dsimp [wmap]
    rw [walkIsOpen_copy]
    exact walkIsOpen_map_cubicEmbedHom hmd w hopen

/-- Vertices in the open cluster of a prescribed vertex, using the production cubic graph and
open walks. This is the literal cluster object corresponding to Grimmett's `C_x(ω)`. -/
def cubicOpenClusterFrom (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) : Set (Cubic d) :=
  {y | ∃ w : (cubicGraph d).Walk x y, walkIsOpen ω w}

/-- The open cluster of the origin, Grimmett's `C_0(ω)`. -/
def cubicOpenCluster (d : ℕ) (ω : EdgeConfiguration d) : Set (Cubic d) :=
  cubicOpenClusterFrom d ω cubicOrigin

/-- The origin has arbitrarily long open self-avoiding walks. This is the path-length event used
for the path-counting union bound, and is proved equivalent to infinitude of `C_0(ω)` below. -/
def hasArbitrarilyLongOpenPaths (d : ℕ) (ω : EdgeConfiguration d) : Prop :=
  ∀ n : ℕ, hasOpenPathOfLengthAtLeast d ω n

/-- A prescribed vertex has arbitrarily long open self-avoiding walks. This vertex-rooted form is
the natural output of the planar no-closed-dual-circuit separation lemma before the box-open event
connects the box back to the origin. -/
def hasArbitrarilyLongOpenPathsFrom (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) : Prop :=
  ∀ n : ℕ, hasOpenPathOfLengthAtLeastFrom d ω x n

/-- Textbook infinite open-cluster event: the open cluster of the origin is infinite. -/
def hasInfiniteOpenCluster (d : ℕ) (ω : EdgeConfiguration d) : Prop :=
  (cubicOpenCluster d ω).Infinite

/-- Textbook vertex-rooted infinite open-cluster event: the open cluster of `x` is infinite. -/
def hasInfiniteOpenClusterFrom (d : ℕ) (ω : EdgeConfiguration d) (x : Cubic d) : Prop :=
  (cubicOpenClusterFrom d ω x).Infinite

@[simp]
theorem hasArbitrarilyLongOpenPathsFrom_origin {d : ℕ} {ω : EdgeConfiguration d} :
    hasArbitrarilyLongOpenPathsFrom d ω cubicOrigin ↔
      hasArbitrarilyLongOpenPaths d ω :=
  Iff.rfl

@[simp]
theorem hasInfiniteOpenClusterFrom_origin {d : ℕ} {ω : EdgeConfiguration d} :
    hasInfiniteOpenClusterFrom d ω cubicOrigin ↔ hasInfiniteOpenCluster d ω :=
  Iff.rfl

/-- Vertices visited by a finite word of signed coordinate directions, starting from `x`. -/
def cubicVerticesFrom {d : ℕ} (x : Cubic d) : List (CubicDirection d) → List (Cubic d)
  | [] => [x]
  | a :: steps => x :: cubicVerticesFrom (cubicStepFrom x a) steps

/-- Endpoint after following a finite word of signed coordinate directions from `x`. -/
def cubicEndpointFrom {d : ℕ} (x : Cubic d) : List (CubicDirection d) → Cubic d
  | [] => x
  | a :: steps => cubicEndpointFrom (cubicStepFrom x a) steps

@[simp]
theorem cubicEndpointFrom_append {d : ℕ} (x : Cubic d)
    (steps₁ steps₂ : List (CubicDirection d)) :
    cubicEndpointFrom x (steps₁ ++ steps₂) =
      cubicEndpointFrom (cubicEndpointFrom x steps₁) steps₂ := by
  induction steps₁ generalizing x with
  | nil => rfl
  | cons a steps₁ ih =>
      simp [cubicEndpointFrom, ih]

/-- Endpoint after repeatedly stepping in the positive `i` direction. -/
theorem cubicEndpointFrom_replicate_pos {d : ℕ} (x : Cubic d) (i : Fin d) (n : ℕ) :
    cubicEndpointFrom x (List.replicate n (i, true)) =
      Function.update x i (x i + (n : ℤ)) := by
  induction n generalizing x with
  | zero =>
      ext j
      by_cases hji : j = i
      · subst hji
        simp [cubicEndpointFrom]
      · simp [cubicEndpointFrom, Function.update_of_ne hji]
  | succ n ih =>
      rw [List.replicate_succ, cubicEndpointFrom, ih]
      ext j
      by_cases hji : j = i
      · subst hji
        simp [cubicStepFrom, cubicDirectionIncrement]
        omega
      · simp [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji]

/-- Endpoint after repeatedly stepping in the negative `i` direction. -/
theorem cubicEndpointFrom_replicate_neg {d : ℕ} (x : Cubic d) (i : Fin d) (n : ℕ) :
    cubicEndpointFrom x (List.replicate n (i, false)) =
      Function.update x i (x i - (n : ℤ)) := by
  induction n generalizing x with
  | zero =>
      ext j
      by_cases hji : j = i
      · subst hji
        simp [cubicEndpointFrom]
      · simp [cubicEndpointFrom, Function.update_of_ne hji]
  | succ n ih =>
      rw [List.replicate_succ, cubicEndpointFrom, ih]
      ext j
      by_cases hji : j = i
      · subst hji
        simp [cubicStepFrom, cubicDirectionIncrement]
        omega
      · simp [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji]

/-- Follow a finite word of signed coordinate directions as an actual graph walk. -/
def cubicWalkFrom {d : ℕ} (x : Cubic d) :
    (steps : List (CubicDirection d)) → (cubicGraph d).Walk x (cubicEndpointFrom x steps)
  | [] => SimpleGraph.Walk.nil
  | a :: steps =>
      SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom x a)
        (cubicWalkFrom (cubicStepFrom x a) steps)

@[simp]
theorem cubicWalkFrom_length {d : ℕ} (x : Cubic d) (steps : List (CubicDirection d)) :
    (cubicWalkFrom x steps).length = steps.length := by
  induction steps generalizing x with
  | nil => rfl
  | cons a steps ih =>
      change (cubicWalkFrom (cubicStepFrom x a) steps).length + 1 = steps.length + 1
      rw [ih]

@[simp]
theorem cubicWalkFrom_support {d : ℕ} (x : Cubic d) (steps : List (CubicDirection d)) :
    (cubicWalkFrom x steps).support = cubicVerticesFrom x steps := by
  induction steps generalizing x with
  | nil => rfl
  | cons a steps ih =>
      change x :: (cubicWalkFrom (cubicStepFrom x a) steps).support =
        x :: cubicVerticesFrom (cubicStepFrom x a) steps
      rw [ih]

/-- A direction word whose visited vertices are nodup gives a graph-theoretic path. -/
theorem cubicWalkFrom_isPath {d : ℕ} {x : Cubic d} {steps : List (CubicDirection d)}
    (h : (cubicVerticesFrom x steps).Nodup) :
    (cubicWalkFrom x steps).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, cubicWalkFrom_support]
  exact h

/-- Every cubic-lattice graph walk is represented by some finite word of signed coordinate
directions. The represented walk agrees with the original after copying across the endpoint
equality tracked by the word. -/
theorem exists_cubicWalkFrom_copy_eq {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) :
    ∃ steps : List (CubicDirection d), ∃ hend : cubicEndpointFrom u steps = v,
      (cubicWalkFrom u steps).copy rfl hend = w ∧ steps.length = w.length := by
  induction w with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | @cons u₀ v₀ w₀ h p ih =>
      rcases (cubicGraph_adj_iff_exists_stepFrom u₀ v₀).mp h with ⟨a, ha⟩
      subst v₀
      rcases ih with ⟨steps, hend, heq, hlen⟩
      refine ⟨a :: steps, ?_, ?_, ?_⟩
      · simp [cubicEndpointFrom, hend]
      · change (SimpleGraph.Walk.cons (cubicGraph_adj_stepFrom u₀ a)
            (cubicWalkFrom (cubicStepFrom u₀ a) steps)).copy rfl _ =
          SimpleGraph.Walk.cons h p
        rw [SimpleGraph.Walk.copy_cons]
        simp [heq]
      · simp [hlen]

/-- Every vertex in an open walk from `x` lies in the open cluster of `x`. -/
theorem mem_cubicOpenClusterFrom_of_mem_support {d : ℕ} {ω : EdgeConfiguration d}
    {x y z : Cubic d} {w : (cubicGraph d).Walk x y}
    (hopen : walkIsOpen ω w) (hz : z ∈ w.support) :
    z ∈ cubicOpenClusterFrom d ω x := by
  induction w with
  | nil =>
      rw [SimpleGraph.Walk.mem_support_nil_iff] at hz
      subst z
      exact ⟨SimpleGraph.Walk.nil, by intro e he; cases he⟩
  | @cons u v y huv p ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨SimpleGraph.Walk.nil, by intro e he; cases he⟩
      · have hopen_tail : walkIsOpen ω p := by
          intro e he
          exact hopen e (by simp [SimpleGraph.Walk.edges_cons, he])
        rcases ih hopen_tail hz with ⟨q, hqopen⟩
        refine ⟨SimpleGraph.Walk.cons huv q, ?_⟩
        intro a ha
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at ha
        rcases ha with hhead | htail
        · subst a
          exact hopen _ (by simp [SimpleGraph.Walk.edges_cons])
        · exact hqopen a htail

/-- The finite set of endpoints reachable from `x` by a signed direction word of length `< n`. -/
def cubicEndpointsOfLengthLT (d : ℕ) (x : Cubic d) (n : ℕ) : Set (Cubic d) :=
  {y | ∃ k : Fin n, ∃ steps : List.Vector (CubicDirection d) (k : ℕ),
    y = cubicEndpointFrom x steps.toList}

/-- There are only finitely many endpoints of signed direction words of length `< n`. -/
theorem cubicEndpointsOfLengthLT_finite (d : ℕ) (x : Cubic d) (n : ℕ) :
    (cubicEndpointsOfLengthLT d x n).Finite := by
  classical
  let f : (Σ k : Fin n, List.Vector (CubicDirection d) (k : ℕ)) → Cubic d :=
    fun a ↦ cubicEndpointFrom x a.2.toList
  refine (Set.finite_range f).subset ?_
  intro y hy
  rcases hy with ⟨k, steps, rfl⟩
  exact ⟨⟨k, steps⟩, rfl⟩

/-- If there is no open self-avoiding path of length at least `n` from `x`, the open cluster of
`x` is contained in the finite set of endpoints of words of length `< n`. -/
theorem cubicOpenClusterFrom_subset_endpointsOfLengthLT_of_not_hasOpenPathOfLengthAtLeastFrom
    {d n : ℕ} {ω : EdgeConfiguration d} {x : Cubic d}
    (hno : ¬ hasOpenPathOfLengthAtLeastFrom d ω x n) :
    cubicOpenClusterFrom d ω x ⊆ cubicEndpointsOfLengthLT d x n := by
  intro y hy
  rcases hy with ⟨w, hopen⟩
  classical
  let q : (cubicGraph d).Walk x y := w.toPath
  have hqpath : q.IsPath := w.toPath.property
  have hqopen : walkIsOpen ω q := by
    dsimp [q]
    exact walkIsOpen_toPath w hopen
  have hlen_lt : q.length < n := by
    by_contra hnot
    exact hno ⟨y, q, hqpath, le_of_not_gt hnot, hqopen⟩
  rcases exists_cubicWalkFrom_copy_eq q with ⟨steps, hend, _heq, hlen⟩
  refine ⟨⟨q.length, hlen_lt⟩, ⟨steps, hlen⟩, ?_⟩
  exact hend.symm

/-- If no open self-avoiding path of length at least `n` starts at `x`, then the open cluster of
`x` is finite. -/
theorem cubicOpenClusterFrom_finite_of_not_hasOpenPathOfLengthAtLeastFrom {d n : ℕ}
    {ω : EdgeConfiguration d} {x : Cubic d}
    (hno : ¬ hasOpenPathOfLengthAtLeastFrom d ω x n) :
    (cubicOpenClusterFrom d ω x).Finite :=
  (cubicEndpointsOfLengthLT_finite d x n).subset
    (cubicOpenClusterFrom_subset_endpointsOfLengthLT_of_not_hasOpenPathOfLengthAtLeastFrom hno)

/-- Arbitrarily long open self-avoiding paths from `x` imply that the textbook open cluster of
`x` is infinite. -/
theorem hasInfiniteOpenClusterFrom_of_hasArbitrarilyLongOpenPathsFrom {d : ℕ}
    {ω : EdgeConfiguration d} {x : Cubic d}
    (hpaths : hasArbitrarilyLongOpenPathsFrom d ω x) :
    hasInfiniteOpenClusterFrom d ω x := by
  rw [hasInfiniteOpenClusterFrom, ← Set.not_finite]
  intro hfinite
  let n := (cubicOpenClusterFrom d ω x).ncard
  rcases hpaths n with ⟨y, w, hwpath, hlen, hopen⟩
  let supportSet : Set (Cubic d) := {z | z ∈ w.support}
  have hsupport_finite : supportSet.Finite := by
    classical
    refine (Set.finite_range (fun i : Fin w.support.length ↦ w.support.get i)).subset ?_
    intro z hz
    rcases List.get_of_mem hz with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  have hsupport_subset : supportSet ⊆ cubicOpenClusterFrom d ω x := by
    intro z hz
    exact mem_cubicOpenClusterFrom_of_mem_support hopen hz
  have hcard_support_le :
      supportSet.ncard ≤ (cubicOpenClusterFrom d ω x).ncard :=
    Set.ncard_le_ncard hsupport_subset hfinite
  have hsupport_card : supportSet.ncard = w.length + 1 := by
    classical
    rw [Set.ncard_eq_toFinset_card supportSet hsupport_finite]
    have htoFinset_eq : hsupport_finite.toFinset = w.support.toFinset := by
      ext z
      simp [supportSet]
    rw [htoFinset_eq, List.toFinset_card_of_nodup hwpath.support_nodup,
      SimpleGraph.Walk.length_support]
  have : w.length + 1 ≤ n := by
    simpa [n, hsupport_card] using hcard_support_le
  omega

/-- The textbook infinite-cluster event at `x` is equivalent, on the locally finite cubic lattice,
to the path-counting event of arbitrarily long open self-avoiding paths from `x`. -/
theorem hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom {d : ℕ}
    {ω : EdgeConfiguration d} {x : Cubic d} :
    hasInfiniteOpenClusterFrom d ω x ↔ hasArbitrarilyLongOpenPathsFrom d ω x := by
  constructor
  · intro hinf n
    by_contra hno
    have hfinite :=
      cubicOpenClusterFrom_finite_of_not_hasOpenPathOfLengthAtLeastFrom
        (d := d) (ω := ω) (x := x) (n := n) hno
    exact (Set.not_finite.mpr hinf) hfinite
  · exact hasInfiniteOpenClusterFrom_of_hasArbitrarilyLongOpenPathsFrom

/-- The textbook infinite origin-cluster event is equivalent to arbitrarily long open
self-avoiding paths from the origin. -/
theorem hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths {d : ℕ}
    {ω : EdgeConfiguration d} :
    hasInfiniteOpenCluster d ω ↔ hasArbitrarilyLongOpenPaths d ω := by
  simpa [hasInfiniteOpenClusterFrom_origin, hasArbitrarilyLongOpenPathsFrom_origin] using
    (hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom
      (d := d) (ω := ω) (x := cubicOrigin))

/-- An infinite open cluster in a pulled-back lower-dimensional configuration embeds as an
infinite open cluster in the ambient configuration. -/
theorem hasInfiniteOpenCluster_cubicConfigurationPullback {m d : ℕ}
    (hmd : m ≤ d) {ω : EdgeConfiguration d} :
    hasInfiniteOpenCluster m (cubicConfigurationPullback hmd ω) →
      hasInfiniteOpenCluster d ω := by
  rw [hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths,
    hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths]
  intro h n
  exact hasOpenPathOfLengthAtLeast_cubicConfigurationPullback hmd (h n)

/-- Infinite open cluster, expressed using exact-length open self-avoiding paths. -/
theorem hasInfiniteOpenCluster_iff_forall_hasOpenPathOfLengthExactly {d : ℕ}
    {ω : EdgeConfiguration d} :
    hasInfiniteOpenCluster d ω ↔ ∀ n : ℕ, hasOpenPathOfLengthExactly d ω n := by
  rw [hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths]
  constructor
  · intro h n
    exact hasOpenPathOfLengthAtLeast_imp_hasOpenPathOfLengthExactly (h n)
  · intro h n
    exact hasOpenPathOfLengthExactly_imp_hasOpenPathOfLengthAtLeast (h n)

/-- Infinite open cluster from a prescribed vertex, expressed using exact-length open
self-avoiding paths. -/
theorem hasInfiniteOpenClusterFrom_iff_forall_hasOpenPathOfLengthExactlyFrom
    {d : ℕ} {ω : EdgeConfiguration d} {x : Cubic d} :
    hasInfiniteOpenClusterFrom d ω x ↔
      ∀ n : ℕ, hasOpenPathOfLengthExactlyFrom d ω x n := by
  rw [hasInfiniteOpenClusterFrom_iff_hasArbitrarilyLongOpenPathsFrom]
  constructor
  · intro h n
    exact hasOpenPathOfLengthAtLeastFrom_imp_hasOpenPathOfLengthExactlyFrom (h n)
  · intro h n
    exact hasOpenPathOfLengthExactlyFrom_imp_hasOpenPathOfLengthAtLeastFrom (h n)

@[simp]
theorem cubicVerticesFrom_nil {d : ℕ} (x : Cubic d) :
    cubicVerticesFrom x ([] : List (CubicDirection d)) = [x] :=
  rfl

@[simp]
theorem cubicVerticesFrom_cons {d : ℕ} (x : Cubic d) (a : CubicDirection d)
    (steps : List (CubicDirection d)) :
    cubicVerticesFrom x (a :: steps) = x :: cubicVerticesFrom (cubicStepFrom x a) steps :=
  rfl

@[simp]
theorem cubicVerticesFrom_length {d : ℕ} (x : Cubic d) (steps : List (CubicDirection d)) :
    (cubicVerticesFrom x steps).length = steps.length + 1 := by
  induction steps generalizing x with
  | nil => simp
  | cons a steps ih => simp [ih]

/-- Changing the starting point translates the entire visited-vertex list. -/
theorem cubicVerticesFrom_eq_map_translate {d : ℕ} (x y : Cubic d)
    (steps : List (CubicDirection d)) :
    cubicVerticesFrom y steps = (cubicVerticesFrom x steps).map (cubicTranslate x y) := by
  induction steps generalizing x y with
  | nil => simp
  | cons a steps ih =>
      rw [cubicVerticesFrom_cons, cubicVerticesFrom_cons, ih (cubicStepFrom x a)
        (cubicStepFrom y a)]
      simp [cubicTranslate_stepFrom]

/-- Vertices of a concatenated direction word are the vertices of the first word, with its final
vertex identified with the initial vertex of the second word. -/
theorem cubicVerticesFrom_append {d : ℕ} (x : Cubic d)
    (steps₁ steps₂ : List (CubicDirection d)) :
    cubicVerticesFrom x (steps₁ ++ steps₂) =
      (cubicVerticesFrom x steps₁).dropLast ++ cubicVerticesFrom
        (cubicEndpointFrom x steps₁) steps₂ := by
  induction steps₁ generalizing x with
  | nil => simp [cubicEndpointFrom]
  | cons a steps₁ ih =>
      have hne : cubicVerticesFrom (cubicStepFrom x a) steps₁ ≠ [] := by
        cases steps₁ <;> simp
      simp [cubicEndpointFrom, ih, List.dropLast_cons_of_ne_nil hne]

/-- The vertices visited after dropping the first `k` directions form a suffix of the full visited
vertex list, when started from the actual vertex reached after those `k` directions. -/
theorem cubicVerticesFrom_drop_suffix {d : ℕ} (x : Cubic d)
    (steps : List (CubicDirection d)) (k : ℕ) :
    cubicVerticesFrom (cubicEndpointFrom x (steps.take k)) (steps.drop k)
      <:+ cubicVerticesFrom x steps := by
  refine ⟨(cubicVerticesFrom x (steps.take k)).dropLast, ?_⟩
  rw [← cubicVerticesFrom_append, List.take_append_drop]

/-- Vertices visited by a length-`n` word of signed coordinate directions from the origin. -/
def cubicVectorVertices {d n : ℕ} (steps : List.Vector (CubicDirection d) n) : List (Cubic d) :=
  cubicVerticesFrom cubicOrigin steps.toList

/-- A length-`n` direction word is self-avoiding when its visited vertices have no repeats. -/
def cubicVectorSelfAvoiding {d n : ℕ} (steps : List.Vector (CubicDirection d) n) : Prop :=
  (cubicVectorVertices steps).Nodup

instance instDecidableCubicVectorSelfAvoiding {d n : ℕ} :
    DecidablePred (cubicVectorSelfAvoiding (d := d) (n := n)) := fun steps => by
  unfold cubicVectorSelfAvoiding cubicVectorVertices
  infer_instance

/-- The first `m` steps of a length `m + n` direction word. -/
def cubicVectorPrefix {d m n : ℕ} (steps : List.Vector (CubicDirection d) (m + n)) :
    List.Vector (CubicDirection d) m :=
  List.Vector.congr (Nat.min_eq_left (Nat.le_add_right m n)) (List.Vector.take m steps)

/-- The last `n` steps of a length `m + n` direction word. -/
def cubicVectorSuffix {d m n : ℕ} (steps : List.Vector (CubicDirection d) (m + n)) :
    List.Vector (CubicDirection d) n :=
  List.Vector.congr (Nat.add_sub_cancel_left m n) (List.Vector.drop m steps)

@[simp]
theorem cubicVectorPrefix_toList {d m n : ℕ}
    (steps : List.Vector (CubicDirection d) (m + n)) :
    (cubicVectorPrefix (m := m) (n := n) steps).toList = steps.toList.take m := by
  cases steps
  rfl

@[simp]
theorem cubicVectorSuffix_toList {d m n : ℕ}
    (steps : List.Vector (CubicDirection d) (m + n)) :
    (cubicVectorSuffix (m := m) (n := n) steps).toList = steps.toList.drop m := by
  cases steps
  rfl

/-- The vertices visited by the first `k` directions form a prefix of the full visited-vertex list. -/
theorem cubicVerticesFrom_take_prefix {d : ℕ} (x : Cubic d)
    (steps : List (CubicDirection d)) (k : ℕ) :
    cubicVerticesFrom x (steps.take k) <+: cubicVerticesFrom x steps := by
  induction steps generalizing x k with
  | nil => simp
  | cons a steps ih =>
      cases k with
      | zero => simp
      | succ k =>
          rcases ih (cubicStepFrom x a) k with ⟨tail, htail⟩
          exact ⟨tail, by simp [htail]⟩

/-- A prefix of a self-avoiding direction word is self-avoiding. -/
theorem cubicVectorSelfAvoiding_prefix {d m n : ℕ}
    {steps : List.Vector (CubicDirection d) (m + n)}
    (h : cubicVectorSelfAvoiding steps) :
    cubicVectorSelfAvoiding (cubicVectorPrefix (m := m) (n := n) steps) := by
  exact h.sublist (cubicVerticesFrom_take_prefix cubicOrigin steps.toList m).sublist

/-- A suffix of a self-avoiding direction word is self-avoiding when translated back to the origin. -/
theorem cubicVectorSelfAvoiding_suffix {d m n : ℕ}
    {steps : List.Vector (CubicDirection d) (m + n)}
    (h : cubicVectorSelfAvoiding steps) :
    cubicVectorSelfAvoiding (cubicVectorSuffix (m := m) (n := n) steps) := by
  unfold cubicVectorSelfAvoiding cubicVectorVertices at h ⊢
  rw [cubicVectorSuffix_toList]
  let base : Cubic d := cubicEndpointFrom cubicOrigin (steps.toList.take m)
  have hsuffix_actual : (cubicVerticesFrom base (steps.toList.drop m)).Nodup :=
    (cubicVerticesFrom_drop_suffix cubicOrigin steps.toList m).nodup h
  have htranslate :
      cubicVerticesFrom base (steps.toList.drop m) =
        (cubicVerticesFrom cubicOrigin (steps.toList.drop m)).map
          (cubicTranslate cubicOrigin base) :=
    cubicVerticesFrom_eq_map_translate cubicOrigin base (steps.toList.drop m)
  rw [htranslate] at hsuffix_actual
  exact List.Nodup.of_map _ hsuffix_actual

/-- If a direction word is realized as a graph-theoretic path from any start, then the same word
translated back to the origin is one of Grimmett's counted self-avoiding walks. -/
theorem cubicVectorSelfAvoiding_of_cubicWalkFrom_isPath {d n : ℕ} {x : Cubic d}
    (steps : List.Vector (CubicDirection d) n)
    (hpath : (cubicWalkFrom x steps.toList).IsPath) :
    cubicVectorSelfAvoiding steps := by
  rw [SimpleGraph.Walk.isPath_def, cubicWalkFrom_support] at hpath
  unfold cubicVectorSelfAvoiding cubicVectorVertices
  have htranslate :
      cubicVerticesFrom x steps.toList =
        (cubicVerticesFrom (cubicOrigin : Cubic d) steps.toList).map
          (cubicTranslate (cubicOrigin : Cubic d) x) :=
    cubicVerticesFrom_eq_map_translate (cubicOrigin : Cubic d) x steps.toList
  rw [htranslate] at hpath
  exact List.Nodup.of_map _ hpath

/-- Every vertex reached after at least one repeated positive step in coordinate `i` has strictly
larger `i`-coordinate than the starting point. -/
theorem cubicVerticesFrom_replicate_pos_coord_lt {d : ℕ} (x : Cubic d) (i : Fin d)
    (n : ℕ) {y : Cubic d}
    (hy : y ∈ cubicVerticesFrom (cubicStepFrom x (i, true))
      (List.replicate n (i, true))) :
    x i < y i := by
  induction n generalizing x y with
  | zero =>
      simp only [List.replicate_zero, cubicVerticesFrom_nil, List.mem_singleton] at hy
      subst hy
      simp [cubicStepFrom, cubicDirectionIncrement]
  | succ n ih =>
      simp only [List.replicate_succ, cubicVerticesFrom_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst hy
        simp [cubicStepFrom, cubicDirectionIncrement]
      · have hstep : x i < cubicStepFrom x (i, true) i := by
          simp [cubicStepFrom, cubicDirectionIncrement]
        exact hstep.trans (ih (cubicStepFrom x (i, true)) hy)

/-- The straight word that repeatedly steps in one positive coordinate direction is self-avoiding. -/
theorem cubicVerticesFrom_replicate_pos_nodup {d : ℕ} (x : Cubic d) (i : Fin d)
    (n : ℕ) :
    (cubicVerticesFrom x (List.replicate n (i, true))).Nodup := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, cubicVerticesFrom_cons, List.nodup_cons]
      constructor
      · intro hxmem
        exact (lt_irrefl (x i)) (cubicVerticesFrom_replicate_pos_coord_lt x i n hxmem)
      · exact ih (cubicStepFrom x (i, true))

/-- Every vertex visited while repeatedly stepping in the positive `i` direction has
`i`-coordinate between the starting coordinate and the final coordinate. -/
theorem cubicVerticesFrom_replicate_pos_coord_between {d : ℕ} (x : Cubic d) (i : Fin d)
    (n : ℕ) {y : Cubic d}
    (hy : y ∈ cubicVerticesFrom x (List.replicate n (i, true))) :
    x i ≤ y i ∧ y i ≤ x i + (n : ℤ) := by
  induction n generalizing x y with
  | zero =>
      simp only [List.replicate_zero, cubicVerticesFrom_nil, List.mem_singleton] at hy
      subst hy
      simp
  | succ n ih =>
      simp only [List.replicate_succ, cubicVerticesFrom_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst hy
        constructor <;> omega
      · have htail := ih (cubicStepFrom x (i, true)) hy
        constructor
        · have : x i + 1 ≤ y i := by
            simpa [cubicStepFrom, cubicDirectionIncrement] using htail.1
          omega
        · have : y i ≤ x i + 1 + (n : ℤ) := by
            simpa [cubicStepFrom, cubicDirectionIncrement] using htail.2
          omega

/-- Repeated positive steps in coordinate `i` leave every other coordinate unchanged. -/
theorem cubicVerticesFrom_replicate_pos_coord_eq_of_ne {d : ℕ} (x : Cubic d)
    (i j : Fin d) (n : ℕ) (hji : j ≠ i) {y : Cubic d}
    (hy : y ∈ cubicVerticesFrom x (List.replicate n (i, true))) :
    y j = x j := by
  induction n generalizing x y with
  | zero =>
      simp only [List.replicate_zero, cubicVerticesFrom_nil, List.mem_singleton] at hy
      subst hy
      rfl
  | succ n ih =>
      simp only [List.replicate_succ, cubicVerticesFrom_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst hy
        rfl
      · have htail := ih (cubicStepFrom x (i, true)) hy
        simpa [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji] using htail

/-- Every vertex visited while repeatedly stepping in the negative `i` direction has
`i`-coordinate between the final coordinate and the starting coordinate. -/
theorem cubicVerticesFrom_replicate_neg_coord_between {d : ℕ} (x : Cubic d) (i : Fin d)
    (n : ℕ) {y : Cubic d}
    (hy : y ∈ cubicVerticesFrom x (List.replicate n (i, false))) :
    x i - (n : ℤ) ≤ y i ∧ y i ≤ x i := by
  induction n generalizing x y with
  | zero =>
      simp only [List.replicate_zero, cubicVerticesFrom_nil, List.mem_singleton] at hy
      subst hy
      simp
  | succ n ih =>
      simp only [List.replicate_succ, cubicVerticesFrom_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst hy
        constructor <;> omega
      · have htail := ih (cubicStepFrom x (i, false)) hy
        constructor
        · have : x i - 1 - (n : ℤ) ≤ y i := by
            simpa [cubicStepFrom, cubicDirectionIncrement] using htail.1
          omega
        · have : y i + 1 ≤ x i := by
            simpa [cubicStepFrom, cubicDirectionIncrement] using htail.2
          omega

/-- Repeated negative steps in coordinate `i` leave every other coordinate unchanged. -/
theorem cubicVerticesFrom_replicate_neg_coord_eq_of_ne {d : ℕ} (x : Cubic d)
    (i j : Fin d) (n : ℕ) (hji : j ≠ i) {y : Cubic d}
    (hy : y ∈ cubicVerticesFrom x (List.replicate n (i, false))) :
    y j = x j := by
  induction n generalizing x y with
  | zero =>
      simp only [List.replicate_zero, cubicVerticesFrom_nil, List.mem_singleton] at hy
      subst hy
      rfl
  | succ n ih =>
      simp only [List.replicate_succ, cubicVerticesFrom_cons, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst hy
        rfl
      · have htail := ih (cubicStepFrom x (i, false)) hy
        simpa [cubicStepFrom, cubicDirectionIncrement, Function.update_of_ne hji] using htail

/-- Self-avoiding walks of length `n` from the origin, encoded as finite words in the `2d`
signed coordinate directions. This is Grimmett's `σ(n)` counting model. -/
abbrev SelfAvoidingWalk (d n : ℕ) :=
  {steps : List.Vector (CubicDirection d) n // cubicVectorSelfAvoiding steps}

/-- Package a path-realized direction word as a counted self-avoiding walk by translating its
starting vertex to the origin. -/
def selfAvoidingWalkOfPathWord {d n : ℕ} {x : Cubic d}
    (steps : List.Vector (CubicDirection d) n)
    (hpath : (cubicWalkFrom x steps.toList).IsPath) : SelfAvoidingWalk d n :=
  ⟨steps, cubicVectorSelfAvoiding_of_cubicWalkFrom_isPath steps hpath⟩

/-- Casting a counted self-avoiding walk across an equality of lengths does not change its
underlying direction word. -/
theorem selfAvoidingWalk_cast_toList {d m n : ℕ} (h : m = n)
    (steps : SelfAvoidingWalk d m) :
    ((cast (by rw [h] : SelfAvoidingWalk d m = SelfAvoidingWalk d n) steps :
      SelfAvoidingWalk d n).1.toList = steps.1.toList) := by
  subst n
  rfl

/-- The graph walk represented by a counted self-avoiding direction word. -/
def selfAvoidingWalkWalk {d n : ℕ} (steps : SelfAvoidingWalk d n) :
    (cubicGraph d).Walk cubicOrigin (cubicEndpointFrom cubicOrigin steps.1.toList) :=
  cubicWalkFrom cubicOrigin steps.1.toList

@[simp]
theorem selfAvoidingWalkWalk_length {d n : ℕ} (steps : SelfAvoidingWalk d n) :
    (selfAvoidingWalkWalk steps).length = n := by
  simp [selfAvoidingWalkWalk]

/-- The graph walk represented by a counted self-avoiding direction word is a path. -/
theorem selfAvoidingWalkWalk_isPath {d n : ℕ} (steps : SelfAvoidingWalk d n) :
    (selfAvoidingWalkWalk steps).IsPath :=
  cubicWalkFrom_isPath steps.2

/-- The number `σ(n)` of self-avoiding walks of length `n` from the origin. -/
noncomputable def selfAvoidingWalkCount (d n : ℕ) : ℕ :=
  Fintype.card (SelfAvoidingWalk d n)

/-- A concrete straight self-avoiding walk of length `n` in any nonzero dimension. -/
def straightSelfAvoidingWalk {d : ℕ} (hd : 0 < d) (n : ℕ) : SelfAvoidingWalk d n :=
  let i : Fin d := ⟨0, hd⟩
  ⟨List.Vector.replicate n (i, true), by
    unfold cubicVectorSelfAvoiding cubicVectorVertices
    simpa [List.Vector.replicate] using
      cubicVerticesFrom_replicate_pos_nodup (cubicOrigin (d := d)) i n⟩

/-- There is at least one self-avoiding walk of every length in any nonzero dimension. -/
theorem one_le_selfAvoidingWalkCount {d : ℕ} (hd : 0 < d) (n : ℕ) :
    1 ≤ selfAvoidingWalkCount d n := by
  simpa [selfAvoidingWalkCount] using
    Fintype.card_pos_iff.mpr ⟨straightSelfAvoidingWalk hd n⟩

/-- Split a length `m + n` self-avoiding word into its self-avoiding prefix and remaining
direction word. -/
def selfAvoidingWalkSplitEmbedding (d m n : ℕ) :
    SelfAvoidingWalk d (m + n) ↪ SelfAvoidingWalk d m × List.Vector (CubicDirection d) n where
  toFun steps :=
    (⟨cubicVectorPrefix (m := m) (n := n) steps.1,
        cubicVectorSelfAvoiding_prefix steps.2⟩,
      cubicVectorSuffix (m := m) (n := n) steps.1)
  inj' := by
    intro steps₁ steps₂ h
    apply Subtype.ext
    apply List.Vector.toList_injective
    have hprefix :
        (cubicVectorPrefix (m := m) (n := n) steps₁.1).toList =
          (cubicVectorPrefix (m := m) (n := n) steps₂.1).toList :=
      congrArg (fun steps : SelfAvoidingWalk d m => steps.1.toList) (congrArg Prod.fst h)
    have hsuffix :
        (cubicVectorSuffix (m := m) (n := n) steps₁.1).toList =
          (cubicVectorSuffix (m := m) (n := n) steps₂.1).toList :=
      congrArg List.Vector.toList (congrArg Prod.snd h)
    calc
      steps₁.1.toList = steps₁.1.toList.take m ++ steps₁.1.toList.drop m := by
        rw [List.take_append_drop]
      _ = steps₂.1.toList.take m ++ steps₂.1.toList.drop m := by
        rw [← cubicVectorPrefix_toList (m := m) (n := n) steps₁.1,
          ← cubicVectorSuffix_toList (m := m) (n := n) steps₁.1, hprefix, hsuffix,
          cubicVectorPrefix_toList, cubicVectorSuffix_toList]
      _ = steps₂.1.toList := by
        rw [List.take_append_drop]

/-- Split a length `m + n` self-avoiding word into self-avoiding words of lengths `m` and `n`. -/
def selfAvoidingWalkSubmultiplicativeEmbedding (d m n : ℕ) :
    SelfAvoidingWalk d (m + n) ↪ SelfAvoidingWalk d m × SelfAvoidingWalk d n where
  toFun steps :=
    (⟨cubicVectorPrefix (m := m) (n := n) steps.1,
        cubicVectorSelfAvoiding_prefix steps.2⟩,
      ⟨cubicVectorSuffix (m := m) (n := n) steps.1,
        cubicVectorSelfAvoiding_suffix steps.2⟩)
  inj' := by
    intro steps₁ steps₂ h
    apply Subtype.ext
    apply List.Vector.toList_injective
    have hprefix :
        (cubicVectorPrefix (m := m) (n := n) steps₁.1).toList =
          (cubicVectorPrefix (m := m) (n := n) steps₂.1).toList :=
      congrArg (fun steps : SelfAvoidingWalk d m => steps.1.toList) (congrArg Prod.fst h)
    have hsuffix :
        (cubicVectorSuffix (m := m) (n := n) steps₁.1).toList =
          (cubicVectorSuffix (m := m) (n := n) steps₂.1).toList :=
      congrArg (fun steps : SelfAvoidingWalk d n => steps.1.toList) (congrArg Prod.snd h)
    calc
      steps₁.1.toList = steps₁.1.toList.take m ++ steps₁.1.toList.drop m := by
        rw [List.take_append_drop]
      _ = steps₂.1.toList.take m ++ steps₂.1.toList.drop m := by
        rw [← cubicVectorPrefix_toList (m := m) (n := n) steps₁.1,
          ← cubicVectorSuffix_toList (m := m) (n := n) steps₁.1, hprefix, hsuffix,
          cubicVectorPrefix_toList, cubicVectorSuffix_toList]
      _ = steps₂.1.toList := by
        rw [List.take_append_drop]

/-- The ambient type of length-`n` direction words has cardinality `(2d)^n`. -/
theorem card_cubicDirection_vector (d n : ℕ) :
    Fintype.card (List.Vector (CubicDirection d) n) = (2 * d) ^ n := by
  rw [card_vector]
  simp [CubicDirection, Nat.mul_comm]

/-- The elementary first counting bound: self-avoiding walks are at most all direction words. -/
theorem selfAvoidingWalkCount_le_directionWords (d n : ℕ) :
    selfAvoidingWalkCount d n ≤ (2 * d) ^ n := by
  classical
  calc
    selfAvoidingWalkCount d n ≤ Fintype.card (List.Vector (CubicDirection d) n) := by
      simpa [selfAvoidingWalkCount, SelfAvoidingWalk] using
        Fintype.card_subtype_le (cubicVectorSelfAvoiding (d := d) (n := n))
    _ = (2 * d) ^ n := card_cubicDirection_vector d n

/-- A first split-counting inequality: after the first `m` self-avoiding steps, the remaining
`n` steps are bounded by all direction words. -/
theorem selfAvoidingWalkCount_le_mul_directionWords (d m n : ℕ) :
    selfAvoidingWalkCount d (m + n) ≤ selfAvoidingWalkCount d m * (2 * d) ^ n := by
  classical
  calc
    selfAvoidingWalkCount d (m + n) ≤
        Fintype.card (SelfAvoidingWalk d m × List.Vector (CubicDirection d) n) := by
      simpa [selfAvoidingWalkCount] using
        Fintype.card_le_of_embedding (selfAvoidingWalkSplitEmbedding d m n)
    _ = selfAvoidingWalkCount d m * Fintype.card (List.Vector (CubicDirection d) n) := by
      simp [selfAvoidingWalkCount]
    _ = selfAvoidingWalkCount d m * (2 * d) ^ n := by
      rw [card_cubicDirection_vector]

/-- Grimmett's submultiplicativity of the self-avoiding-walk counts `σ(m+n) ≤ σ(m)σ(n)`. -/
theorem selfAvoidingWalkCount_submultiplicative (d m n : ℕ) :
    selfAvoidingWalkCount d (m + n) ≤ selfAvoidingWalkCount d m * selfAvoidingWalkCount d n := by
  classical
  calc
    selfAvoidingWalkCount d (m + n) ≤
        Fintype.card (SelfAvoidingWalk d m × SelfAvoidingWalk d n) := by
      simpa [selfAvoidingWalkCount] using
        Fintype.card_le_of_embedding (selfAvoidingWalkSubmultiplicativeEmbedding d m n)
    _ = selfAvoidingWalkCount d m * selfAvoidingWalkCount d n := by
      simp [selfAvoidingWalkCount]

end Percolation
