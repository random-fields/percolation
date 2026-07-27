import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Algebra.BigOperators.Ring.Nat
import Percolation.Critical.Basic
import Percolation.Planar.Basic

/-!
# Planar Peierls tail bridge

This file connects the planar closed-dual-circuit estimates to the critical-layer connective
constant bounds. It is still conditional on the geometric separation and circuit-encoding facts:
once those supply length-indexed finite families of dual circuits around the origin, the theorems
below turn Grimmett's Peierls majorant into vanishing tail probabilities.
-/

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

lemma sym2_eq_edge_iff_of_adj {u v w : V} (huv : G.Adj u v) :
    s(v, w) = s(u, v) ↔ w = u := by
  constructor
  · intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨hvu, _hwv⟩ | ⟨_hvv, hwu⟩
    · exact False.elim (huv.ne hvu.symm)
    · exact hwu
  · intro h
    subst h
    exact Sym2.eq_swap

noncomputable instance deleteEdges_neighborSet_fintype [G.LocallyFinite]
    (t : Set (Sym2 V)) (x : V) : Fintype ((G.deleteEdges t).neighborSet x) := by
  classical
  let emb : (G.deleteEdges t).neighborSet x ↪ G.neighborSet x :=
    { toFun := fun y => ⟨y.1, by simpa [deleteEdges_adj] using y.2.1⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        exact congr_arg (fun y : G.neighborSet x => (y : V)) h }
  exact Fintype.ofInjective _ emb.injective

noncomputable instance deleteEdges_locallyFinite [G.LocallyFinite]
    (t : Set (Sym2 V)) : (G.deleteEdges t).LocallyFinite :=
  fun x ↦ deleteEdges_neighborSet_fintype (G := G) t x

lemma degree_deleteEdges_singleton_right [G.LocallyFinite] {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).degree v = G.degree v - 1 := by
  classical
  letI := deleteEdges_neighborSet_fintype (G := G) ({s(u, v)} : Set (Sym2 V)) v
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hfin : (G.deleteEdges {s(u, v)}).neighborFinset v = (G.neighborFinset v).erase u := by
    ext w
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset]
    rw [deleteEdges_adj]
    constructor
    · rintro ⟨hvw, hne⟩
      exact ⟨by
        intro hwu
        apply hne
        rw [Set.mem_singleton_iff]
        subst hwu
        exact Sym2.eq_swap, hvw⟩
    · rintro ⟨hwu, hvw⟩
      exact ⟨hvw, by
        rw [Set.mem_singleton_iff]
        exact fun h => hwu ((sym2_eq_edge_iff_of_adj (G := G) huv).mp h)⟩
  rw [hfin, Finset.card_erase_of_mem]
  simpa [mem_neighborFinset] using huv.symm

lemma degree_deleteEdges_singleton_of_not_endpoint [G.LocallyFinite] {u v x : V}
    (hxu : x ≠ u) (hxv : x ≠ v) :
    (G.deleteEdges {s(u, v)}).degree x = G.degree x := by
  classical
  letI := deleteEdges_neighborSet_fintype (G := G) ({s(u, v)} : Set (Sym2 V)) x
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  congr 1
  ext y
  rw [mem_neighborFinset, mem_neighborFinset, deleteEdges_adj]
  constructor
  · exact fun h => h.1
  · intro hxy
    refine ⟨hxy, ?_⟩
    rw [Set.mem_singleton_iff]
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨hxu', _⟩ | ⟨hxv', _⟩
    · exact hxu hxu'
    · exact hxv hxv'

/-- The degree after deleting a finite edge set is the number of old neighbors whose edge was not
deleted. -/
lemma degree_deleteEdges_finset_eq_card_filter_not [G.LocallyFinite] [DecidableEq V]
    (t : Finset (Sym2 V)) (x : V) :
    (G.deleteEdges (t : Set (Sym2 V))).degree x =
      ((G.neighborFinset x).filter fun y => s(x, y) ∉ (t : Set (Sym2 V))).card := by
  classical
  letI := deleteEdges_neighborSet_fintype (G := G) ((t : Set (Sym2 V))) x
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp [deleteEdges_adj]

/-- Deleting a finite edge set splits the old degree into remaining and deleted incident edges. -/
lemma degree_deleteEdges_finset_add_card_filter [G.LocallyFinite] [DecidableEq V]
    (t : Finset (Sym2 V)) (x : V) :
    (G.deleteEdges (t : Set (Sym2 V))).degree x +
      ((G.neighborFinset x).filter fun y => s(x, y) ∈ (t : Set (Sym2 V))).card =
        G.degree x := by
  classical
  rw [degree_deleteEdges_finset_eq_card_filter_not (G := G) t x]
  rw [← card_neighborFinset_eq_degree]
  rw [add_comm]
  exact Finset.card_filter_add_card_filter_not (s := G.neighborFinset x)
    (p := fun y => s(x, y) ∈ (t : Set (Sym2 V)))

/-- For a trail, incident deleted-neighbor count agrees with the list count of trail edges
incident to the vertex. -/
lemma card_neighborFinset_filter_walk_edges_toFinset_eq_countP
    [G.LocallyFinite] [DecidableEq V]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (x : V) :
    ((G.neighborFinset x).filter fun y =>
      s(x, y) ∈ (p.edges.toFinset : Set (Sym2 V))).card =
      p.edges.countP (fun e => x ∈ e) := by
  classical
  have hcard :
      ((G.neighborFinset x).filter fun y =>
        s(x, y) ∈ (p.edges.toFinset : Set (Sym2 V))).card =
        (p.edges.toFinset.filter fun e => x ∈ e).card := by
    apply Finset.card_bij (fun y _ => s(x, y))
    · intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨hy.2, by simp [Sym2.mem_iff]⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [Finset.mem_filter] at hy₁ hy₂
      have hy₁adj : G.Adj x y₁ := (mem_neighborFinset (G := G) x y₁).mp hy₁.1
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_hxx, hy₁₂⟩ | ⟨_hxy₂, hy₁x⟩
      · exact hy₁₂
      · exact False.elim (hy₁adj.ne hy₁x.symm)
    · intro e he
      rw [Finset.mem_filter] at he
      have he_edges : e ∈ p.edges := by simpa using he.1
      have he_edgeSet : e ∈ G.edgeSet := p.edges_subset_edgeSet he_edges
      rcases (Sym2.mem_iff_exists.mp he.2) with ⟨y, hy⟩
      refine ⟨y, ?_, ?_⟩
      · rw [Finset.mem_filter]
        have hxy : G.Adj x y := by
          simpa [hy, mem_edgeSet] using he_edgeSet
        exact ⟨(mem_neighborFinset (G := G) x y).mpr hxy, by simpa [← hy] using he.1⟩
      · exact hy.symm
  rw [hcard]
  rw [show p.edges.toFinset.filter (fun e => x ∈ e) =
      (p.edges.filter fun e => decide (x ∈ e)).toFinset by
    ext e
    simp]
  rw [List.toFinset_card_of_nodup]
  · rw [← List.countP_eq_length_filter]
  · exact hp.edges_nodup.filter _

/-- Deleting the edge set of a closed trail preserves even degree at every vertex. -/
lemma even_degree_deleteEdges_walk_edges_toFinset_of_isTrail_closed
    [G.LocallyFinite] [DecidableEq V] (hdeg : ∀ x, Even (G.degree x))
    {u : V} {p : G.Walk u u} (hp : p.IsTrail) :
    ∀ x, Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) := by
  intro x
  have hsum := degree_deleteEdges_finset_add_card_filter (G := G) p.edges.toFinset x
  rw [card_neighborFinset_filter_walk_edges_toFinset_eq_countP (G := G) hp x] at hsum
  have hremoved_even : Even (p.edges.countP fun e => x ∈ e) := by
    exact (hp.even_countP_edges_iff x).mpr (by simp)
  have hsum_even :
      Even (((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) +
        p.edges.countP (fun e => x ∈ e)) := by
    rw [hsum]
    exact hdeg x
  exact (Nat.even_add.mp hsum_even).mpr hremoved_even

lemma degree_induce_of_neighborSet_subset_lf {s : Set V} {v : s}
    [Fintype (G.neighborSet (v : V))] [Fintype ((G.induce s).neighborSet v)]
    (h : G.neighborSet (v : V) ⊆ s) :
    (G.induce s).degree v = G.degree (v : V) := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun y => ⟨(y.1 : V), (induce_adj (G := G) (s := s)).mp y.2⟩
      invFun := fun y => ⟨⟨(y : V), h y.2⟩,
        (induce_adj (G := G) (s := s)).mpr y.2⟩
      left_inv := by intro y; ext; rfl
      right_inv := by intro y; ext; rfl }

lemma odd_tsub_one_of_even_pos {n : ℕ} (he : Even n) (hp : 0 < n) : Odd (n - 1) := by
  rcases he with ⟨k, hk⟩
  subst hk
  cases k with
  | zero => simp at hp
  | succ k =>
      use k
      omega

lemma not_odd_of_even {n : ℕ} (he : Even n) : ¬ Odd n :=
  Nat.not_odd_iff_even.mpr he

lemma support_finite_of_edgeSet_finite (h : G.edgeSet.Finite) : G.support.Finite := by
  classical
  refine (h.biUnion (fun e _ => e.toFinset.finite_toSet)).subset ?_
  intro z hz
  rw [mem_support] at hz
  rcases hz with ⟨y, hzy⟩
  refine Set.mem_iUnion.mpr ⟨s(z, y), ?_⟩
  refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
  · simpa [mem_edgeSet] using hzy
  · simp [Sym2.mem_toFinset]

lemma isEdgeReachable_two_of_forall_even_degree_of_finite_support [G.LocallyFinite]
    (hfinite : G.support.Finite) (hdeg : ∀ x, Even (G.degree x))
    {u v : V} (huv : G.Adj u v) :
    G.IsEdgeReachable 2 u v := by
  classical
  by_contra hnot
  have hbridge : G.IsBridge s(u, v) :=
    (isBridge_iff_adj_and_not_isEdgeConnected_two (G := G)).mpr ⟨huv, hnot⟩
  let H : SimpleGraph V := G.deleteEdges {s(u, v)}
  letI (x : V) : Fintype (H.neighborSet x) :=
    deleteEdges_neighborSet_fintype (G := G) ({s(u, v)} : Set (Sym2 V)) x
  let C : Set V := {x | H.Reachable v x}
  have hCfinite : C.Finite := by
    refine hfinite.subset ?_
    intro x hx
    by_cases hxv : x = v
    · simpa [hxv] using huv.right_mem_support
    · have hxreach : H.Reachable v x := by simpa [C] using hx
      have hxH : x ∈ H.support := mem_support_of_reachable (G := H) hxv hxreach.symm
      exact support_mono (G.deleteEdges_le {s(u, v)}) hxH
  letI : Fintype C := hCfinite.fintype
  let HC : SimpleGraph C := H.induce C
  have hvC : v ∈ C := by exact SimpleGraph.Reachable.refl (G := H) (u := v)
  let vC : C := ⟨v, hvC⟩
  have hneighbor_subset : ∀ x : C, H.neighborSet x ⊆ C := by
    intro x y hy
    exact x.property.trans hy.reachable
  have hdeg_induce : ∀ x : C, HC.degree x = H.degree x := by
    intro x
    exact degree_induce_of_neighborSet_subset_lf (G := H) (s := C) (v := x)
      (hneighbor_subset x)
  have hv_odd : Odd (HC.degree vC) := by
    rw [hdeg_induce]
    rw [show H.degree v = G.degree v - 1 by
      exact degree_deleteEdges_singleton_right (G := G) huv]
    exact odd_tsub_one_of_even_pos (hdeg v)
      ((degree_pos (G := G) (v := v)).mpr
        (by simpa [SimpleGraph.IsIsolated] using ⟨u, huv.symm⟩))
  rcases HC.exists_ne_odd_degree_of_exists_odd_degree vC hv_odd with ⟨wC, hw_ne, hw_odd⟩
  have hw_ne_v : (wC : V) ≠ v := by
    intro h
    apply hw_ne
    ext
    exact h
  have hw_ne_u : (wC : V) ≠ u := by
    intro hwu
    have hreach_vu : H.Reachable v u := by simpa [hwu] using wC.property
    exact hbridge.2 hreach_vu.symm
  have hw_even : Even (HC.degree wC) := by
    rw [hdeg_induce]
    rw [show H.degree (wC : V) = G.degree (wC : V) by
      exact degree_deleteEdges_singleton_of_not_endpoint (G := G) hw_ne_u hw_ne_v]
    exact hdeg wC
  exact (not_odd_of_even hw_even) hw_odd

/-- Induction step for extracting an odd marked cycle from a finite even graph.

The marked set `X` is a finite set of graph edges with odd cardinality. The proof picks one
marked edge, finds a simple cycle through it using the no-bridge lemma above, and either that
cycle already meets `X` oddly or deletes the whole cycle and recurses on `X \ cycle`. -/
lemma exists_isCycle_odd_card_filter_of_odd_edge_finset_aux [DecidableEq V] :
    ∀ (n : ℕ),
      (∀ (m : ℕ), m < n →
        ∀ (G : SimpleGraph V) [G.LocallyFinite], G.support.Finite →
          (∀ x, Even (G.degree x)) →
          ∀ X : Finset (Sym2 V), X.card = m →
            (∀ e ∈ X, e ∈ G.edgeSet) → Odd X.card →
              ∃ u : V, ∃ w : G.Walk u u,
                w.IsCycle ∧ Odd ((X.filter fun e => e ∈ w.edges.toFinset).card)) →
        ∀ (G : SimpleGraph V) [G.LocallyFinite], G.support.Finite →
          (∀ x, Even (G.degree x)) →
          ∀ X : Finset (Sym2 V), X.card = n →
            (∀ e ∈ X, e ∈ G.edgeSet) → Odd X.card →
              ∃ u : V, ∃ w : G.Walk u u,
                w.IsCycle ∧ Odd ((X.filter fun e => e ∈ w.edges.toFinset).card) := by
  intro n ih G instG hfinite hdeg X hXcard hXedge hXodd
  classical
  have hXnonempty : X.Nonempty := Finset.card_pos.mp hXodd.pos
  rcases hXnonempty with ⟨e, heX⟩
  induction e using Sym2.ind with
  | h u v =>
      have huv : G.Adj u v := by
        simpa [mem_edgeSet] using hXedge s(u, v) heX
      have h2 : G.IsEdgeReachable 2 u v :=
        isEdgeReachable_two_of_forall_even_degree_of_finite_support hfinite hdeg huv
      have hreach : (G.deleteEdges {s(u, v)}).Reachable u v :=
        (isEdgeReachable_two.mp h2) s(u, v)
      rcases (adj_and_reachable_delete_edges_iff_exists_cycle (G := G) (v := u) (w := v)).mp
          ⟨huv, hreach⟩ with ⟨z, w, hwcycle, hmem⟩
      let C : Finset (Sym2 V) := w.edges.toFinset
      let XC : Finset (Sym2 V) := X.filter fun e ↦ e ∈ C
      by_cases hXCodd : Odd XC.card
      · exact ⟨z, w, hwcycle, by simpa [XC, C] using hXCodd⟩
      · have hXCeven : Even XC.card := Nat.not_odd_iff_even.mp hXCodd
        let X' : Finset (Sym2 V) := X \ C
        let G' : SimpleGraph V := G.deleteEdges (C : Set (Sym2 V))
        have hfinite' : G'.support.Finite := by
          exact hfinite.subset
            (fun x hx ↦ support_mono (G.deleteEdges_le (C : Set (Sym2 V))) hx)
        have hdeg' : ∀ x, Even (G'.degree x) := by
          intro x
          simpa [G', C] using even_degree_deleteEdges_walk_edges_toFinset_of_isTrail_closed
            (G := G) hdeg hwcycle.isTrail x
        have hX'edge : ∀ e ∈ X', e ∈ G'.edgeSet := by
          intro e he
          rw [Finset.mem_sdiff] at he
          rw [edgeSet_deleteEdges]
          exact ⟨hXedge e he.1, he.2⟩
        have hpartition : XC.card + X'.card = X.card := by
          have hnot : X.filter (fun e ↦ e ∉ C) = X' := by
            ext e
            simp [X']
          rw [← hnot]
          exact Finset.card_filter_add_card_filter_not (s := X) (p := fun e ↦ e ∈ C)
        have hX'odd : Odd X'.card := by
          have hsum_odd : Odd (XC.card + X'.card) := by
            rw [hpartition]
            exact hXodd
          by_contra hnot
          have hX'even : Even X'.card := Nat.not_odd_iff_even.mp hnot
          exact (Nat.not_odd_iff_even.mpr (hXCeven.add hX'even)) hsum_odd
        have heC : s(u, v) ∈ C := by simpa [C] using hmem
        have hlt : X'.card < n := by
          have hsub : X' ⊂ X := by
            rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset)]
            exact ⟨s(u, v), heX, by simp [C, heC]⟩
          exact hXcard ▸ Finset.card_lt_card hsub
        rcases ih X'.card hlt G' hfinite' hdeg' X' rfl hX'edge hX'odd with
          ⟨z', w', hw'cycle, hw'odd⟩
        let wG : G.Walk z' z' := w'.mapLe (G.deleteEdges_le (C : Set (Sym2 V)))
        have hwGcycle : wG.IsCycle :=
          hw'cycle.mapLe (G.deleteEdges_le (C : Set (Sym2 V)))
        have hfilter_eq :
            X.filter (fun e ↦ e ∈ wG.edges.toFinset) =
              X'.filter (fun e ↦ e ∈ w'.edges.toFinset) := by
          ext e
          constructor
          · intro he
            rw [Finset.mem_filter] at he
            have hew' : e ∈ w'.edges.toFinset := by
              simpa [wG, Walk.edges_mapLe_eq_edges] using he.2
            have he_edges : e ∈ w'.edges := by simpa using hew'
            have he_notC : e ∉ C := by
              have heG' : e ∈ G'.edgeSet := w'.edges_subset_edgeSet he_edges
              have heG'_split : e ∈ G.edgeSet ∧ e ∉ C := by
                simpa [G', edgeSet_deleteEdges] using heG'
              exact heG'_split.2
            change e ∈ (X \ C).filter (fun e ↦ e ∈ w'.edges.toFinset)
            rw [Finset.mem_filter, Finset.mem_sdiff]
            exact ⟨⟨he.1, he_notC⟩, hew'⟩
          · intro he
            change e ∈ (X \ C).filter (fun e ↦ e ∈ w'.edges.toFinset) at he
            rw [Finset.mem_filter, Finset.mem_sdiff] at he
            rw [Finset.mem_filter]
            exact ⟨he.1.1, by simpa [wG, Walk.edges_mapLe_eq_edges] using he.2⟩
        exact ⟨z', wG, hwGcycle, by rw [hfilter_eq]; exact hw'odd⟩

/-- In a finite-support locally finite graph where every vertex has even degree, every finite odd
set of graph edges contains an odd number of edges from some simple cycle. This is the finite
cycle-selection core of the parity Peierls argument. -/
lemma exists_isCycle_odd_card_filter_of_odd_edge_finset [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (hfinite : G.support.Finite)
    (hdeg : ∀ x, Even (G.degree x)) (X : Finset (Sym2 V))
    (hXedge : ∀ e ∈ X, e ∈ G.edgeSet) (hXodd : Odd X.card) :
    ∃ u : V, ∃ w : G.Walk u u,
      w.IsCycle ∧ Odd ((X.filter fun e ↦ e ∈ w.edges.toFinset).card) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (G : SimpleGraph V) [G.LocallyFinite], G.support.Finite →
      (∀ x, Even (G.degree x)) →
      ∀ X : Finset (Sym2 V), X.card = n →
        (∀ e ∈ X, e ∈ G.edgeSet) → Odd X.card →
          ∃ u : V, ∃ w : G.Walk u u,
            w.IsCycle ∧ Odd ((X.filter fun e ↦ e ∈ w.edges.toFinset).card)
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strong_induction_on n
      (fun n ih ↦ exists_isCycle_odd_card_filter_of_odd_edge_finset_aux (V := V) n ih)
  exact hP X.card G hfinite hdeg X rfl hXedge hXodd

end SimpleGraph

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset unitInterval BigOperators

/-- A finite length window of encoded shifted-dual circuits. This is the event that some circuit
from the families indexed by lengths `N, ..., N + M - 1` is open in the induced dual
configuration. -/
def encodedOpenDualCircuitWindow {β : ℕ → Type*} (circuits : ∀ n, β n → DualCircuit)
    (N M : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ k : Fin M, ∃ b : β (N + (k : ℕ)), (circuits (N + (k : ℕ)) b).IsOpen ω}

@[simp]
theorem mem_encodedOpenDualCircuitWindow {β : ℕ → Type*}
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ encodedOpenDualCircuitWindow circuits N M ↔
      ∃ k : Fin M, ∃ b : β (N + (k : ℕ)),
        (circuits (N + (k : ℕ)) b).IsOpen ω :=
  Iff.rfl

/-- Encoded shifted-dual circuit tail event, i.e. the event that some indexed circuit of length at
least `N` is open in the induced dual configuration. This is the event that later geometric
separation lemmas will instantiate as Grimmett's closed-dual-circuit tail `F_N`. -/
def encodedOpenDualCircuitTail {β : ℕ → Type*} (circuits : ∀ n, β n → DualCircuit)
    (N : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω}

@[simp]
theorem mem_encodedOpenDualCircuitTail {β : ℕ → Type*}
    (circuits : ∀ n, β n → DualCircuit) (N : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ encodedOpenDualCircuitTail circuits N ↔
      ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω :=
  Iff.rfl

/-- Box-indexed encoded shifted-dual circuit tail event. This is closer to Grimmett's notation
`F_N`: for each box scale `N`, the family of relevant circuits may depend on `N`, while the
length index still starts at `N`. -/
def boxIndexedOpenDualCircuitTail {β : ℕ → ℕ → Type*}
    (circuits : ∀ N n, β N n → DualCircuit) (N : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ k : ℕ, ∃ b : β N (N + k), (circuits N (N + k) b).IsOpen ω}

@[simp]
theorem mem_boxIndexedOpenDualCircuitTail {β : ℕ → ℕ → Type*}
    (circuits : ∀ N n, β N n → DualCircuit) (N : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ boxIndexedOpenDualCircuitTail circuits N ↔
      ∃ k : ℕ, ∃ b : β N (N + k), (circuits N (N + k) b).IsOpen ω :=
  Iff.rfl

/-- A finite encoded window is contained in the corresponding tail. -/
theorem encodedOpenDualCircuitWindow_subset_tail {β : ℕ → Type*}
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ) :
    encodedOpenDualCircuitWindow circuits N M ⊆ encodedOpenDualCircuitTail circuits N := by
  intro ω hω
  rcases hω with ⟨k, b, hb⟩
  exact ⟨(k : ℕ), b, hb⟩

/-- Encoded dual-circuit windows increase as the finite length window widens. -/
theorem encodedOpenDualCircuitWindow_monotone {β : ℕ → Type*}
    (circuits : ∀ n, β n → DualCircuit) (N : ℕ) :
    Monotone fun M : ℕ ↦ encodedOpenDualCircuitWindow circuits N M := by
  intro M L hML ω hω
  rcases hω with ⟨k, b, hb⟩
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hML⟩, b, by simpa using hb⟩

/-- The encoded tail is the increasing union of its finite length windows. -/
theorem iUnion_encodedOpenDualCircuitWindow_eq_tail {β : ℕ → Type*}
    (circuits : ∀ n, β n → DualCircuit) (N : ℕ) :
    (⋃ M : ℕ, encodedOpenDualCircuitWindow circuits N M) =
      encodedOpenDualCircuitTail circuits N := by
  ext ω
  constructor
  · intro hω
    rw [Set.mem_iUnion] at hω
    rcases hω with ⟨M, k, b, hb⟩
    exact ⟨(k : ℕ), b, hb⟩
  · intro hω
    rcases hω with ⟨k, b, hb⟩
    rw [Set.mem_iUnion]
    exact ⟨k + 1, ⟨⟨k, Nat.lt_succ_self k⟩, b, by simpa using hb⟩⟩

/-- Encoded dual-circuit tails decrease as the length cutoff increases. -/
theorem encodedOpenDualCircuitTail_antitone {β : ℕ → Type*}
    (circuits : ∀ n, β n → DualCircuit) :
    Antitone (encodedOpenDualCircuitTail circuits) := by
  intro N M hNM ω hω
  rcases hω with ⟨k, b, hb⟩
  refine ⟨M - N + k, ?_⟩
  have hidx : N + (M - N + k) = M + k := by omega
  have htail : ∃ b : β (M + k), (circuits (M + k) b).IsOpen ω := ⟨b, hb⟩
  exact hidx.symm ▸ htail

/-- A finite encoded dual-circuit window is measurable. -/
theorem measurableSet_encodedOpenDualCircuitWindow {β : ℕ → Type*} [∀ n, Fintype (β n)]
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ) :
    MeasurableSet (encodedOpenDualCircuitWindow circuits N M) := by
  rw [show encodedOpenDualCircuitWindow circuits N M =
      ⋃ k : Fin M, ⋃ b : β (N + (k : ℕ)), {ω : EdgeConfiguration 2 |
        (circuits (N + (k : ℕ)) b).IsOpen ω} by
    ext ω
    simp [encodedOpenDualCircuitWindow]]
  exact MeasurableSet.iUnion fun k : Fin M ↦
    MeasurableSet.iUnion fun b : β (N + (k : ℕ)) ↦
      DualCircuit.measurableSet_isOpen _

/-- The finite primal support crossed by all shifted-dual circuits in the encoded window
`N, ..., N + M - 1`. This is the support whose disjointness from Grimmett's finite open event
`G_N` gives finite-window independence. -/
noncomputable def encodedOpenDualCircuitWindowPrimalSupport {β : ℕ → Type*}
    [∀ n, Fintype (β n)] (circuits : ∀ n, β n → DualCircuit)
    (N M : ℕ) : Finset (CubicEdge 2) := by
  classical
  exact Finset.univ.biUnion fun k : Fin M ↦
    Finset.univ.biUnion fun b : β (N + (k : ℕ)) ↦
      (circuits (N + (k : ℕ)) b).crossedPrimalEdgeFinset

/-- Each circuit in a finite encoded window has its crossed primal bonds contained in the
window's combined primal support. -/
theorem crossedPrimalEdgeFinset_subset_encodedOpenDualCircuitWindowPrimalSupport
    {β : ℕ → Type*} [∀ n, Fintype (β n)]
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ)
    (k : Fin M) (b : β (N + (k : ℕ))) :
    (circuits (N + (k : ℕ)) b).crossedPrimalEdgeFinset ⊆
      encodedOpenDualCircuitWindowPrimalSupport circuits N M := by
  classical
  intro e he
  simp only [encodedOpenDualCircuitWindowPrimalSupport, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  exact ⟨k, b, he⟩

/-- To prove that a finite encoded window has no crossed primal bond in a finite open support, it
is enough to prove that fact for each individual circuit in the window. This is the form expected
from the concrete planar geometry: a circuit surrounding `B(N)` crosses no bond inside `B(N)`. -/
theorem disjoint_encodedOpenDualCircuitWindowPrimalSupport_of_forall
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (s : Finset (CubicEdge 2))
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ)
    (h : ∀ (k : Fin M) (b : β (N + (k : ℕ))),
      Disjoint ((s : Finset (CubicEdge 2)) : Set (CubicEdge 2))
        (((circuits (N + (k : ℕ)) b).crossedPrimalEdgeFinset : Finset (CubicEdge 2)) :
          Set (CubicEdge 2))) :
    Disjoint ((s : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      ((encodedOpenDualCircuitWindowPrimalSupport circuits N M : Finset (CubicEdge 2)) :
        Set (CubicEdge 2)) := by
  classical
  rw [Set.disjoint_left]
  intro e hes he
  simp only [encodedOpenDualCircuitWindowPrimalSupport, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and] at he
  rcases he with ⟨k, b, heb⟩
  have hkb := h k b
  rw [Set.disjoint_left] at hkb
  exact hkb hes heb

/-- A finite encoded dual-circuit window is measurable with respect to the finite coordinate
sigma-algebra generated by the primal bonds crossed by circuits in that window. -/
theorem measurableSet_encodedOpenDualCircuitWindow_edgeCoordinateMeasurableSpace
    {β : ℕ → Type*} [∀ n, Fintype (β n)]
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ) :
    MeasurableSet[edgeCoordinateMeasurableSpace 2
      (encodedOpenDualCircuitWindowPrimalSupport circuits N M)]
      (encodedOpenDualCircuitWindow circuits N M) := by
  classical
  rw [show encodedOpenDualCircuitWindow circuits N M =
      ⋃ k : Fin M, ⋃ b : β (N + (k : ℕ)), {ω : EdgeConfiguration 2 |
        (circuits (N + (k : ℕ)) b).IsOpen ω} by
    ext ω
    simp [encodedOpenDualCircuitWindow]]
  exact MeasurableSet.iUnion fun k : Fin M ↦
    MeasurableSet.iUnion fun b : β (N + (k : ℕ)) ↦
      (edgeCoordinateMeasurableSpace_mono 2
        (crossedPrimalEdgeFinset_subset_encodedOpenDualCircuitWindowPrimalSupport
          circuits N M k b))
        _ (DualCircuit.measurableSet_isOpen_edgeCoordinateMeasurableSpace _)

/-- Finite-support form of Grimmett's `G_m`/`F_{m,M}` independence step: if the primal support of
`G_m` is disjoint from all primal bonds crossed by circuits in the finite encoded window, then the
finite open event is independent of that window. -/
theorem indepSet_openEdgeSetEvent_encodedOpenDualCircuitWindow_of_disjoint_support
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (s : Finset (CubicEdge 2)) (circuits : ∀ n, β n → DualCircuit) (N M : ℕ)
    (hdisj : Disjoint (s : Set (CubicEdge 2))
      ((encodedOpenDualCircuitWindowPrimalSupport circuits N M : Finset (CubicEdge 2)) :
        Set (CubicEdge 2))) :
    IndepSet (openEdgeSetEvent 2 s) (encodedOpenDualCircuitWindow circuits N M)
      (bernoulliBondMeasure 2 p) :=
  bernoulliBondMeasure_indepSet_of_measurableSet_edgeCoordinateMeasurableSpace 2 p s
    (encodedOpenDualCircuitWindowPrimalSupport circuits N M) hdisj
    (measurableSet_openEdgeSetEvent_edgeCoordinateMeasurableSpace 2 s)
    (measurableSet_encodedOpenDualCircuitWindow_edgeCoordinateMeasurableSpace circuits N M)

/-- An encoded dual-circuit tail is measurable. -/
theorem measurableSet_encodedOpenDualCircuitTail {β : ℕ → Type*} [∀ n, Fintype (β n)]
    (circuits : ∀ n, β n → DualCircuit) (N : ℕ) :
    MeasurableSet (encodedOpenDualCircuitTail circuits N) := by
  rw [show encodedOpenDualCircuitTail circuits N =
      ⋃ k : ℕ, ⋃ b : β (N + k), {ω : EdgeConfiguration 2 |
        (circuits (N + k) b).IsOpen ω} by
    ext ω
    simp [encodedOpenDualCircuitTail]]
  exact MeasurableSet.iUnion fun k : ℕ ↦
    MeasurableSet.iUnion fun b : β (N + k) ↦ DualCircuit.measurableSet_isOpen _

/-- A box-indexed encoded dual-circuit tail is measurable. -/
theorem measurableSet_boxIndexedOpenDualCircuitTail
    {β : ℕ → ℕ → Type*} [∀ N n, Fintype (β N n)]
    (circuits : ∀ N n, β N n → DualCircuit) (N : ℕ) :
    MeasurableSet (boxIndexedOpenDualCircuitTail circuits N) := by
  letI : ∀ n, Fintype (β N n) := fun n ↦ inferInstance
  simpa [boxIndexedOpenDualCircuitTail, encodedOpenDualCircuitTail] using
    (measurableSet_encodedOpenDualCircuitTail (fun n ↦ circuits N n) N)

/-- Independence is preserved when the second event is an increasing countable union. This is the
measure-continuity bridge used to pass from finite Peierls windows to the closed-dual-circuit
tail `F_m`. -/
theorem indepSet_iUnion_of_monotone {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Set Ω} {F : ℕ → Set Ω}
    (hAmeas : MeasurableSet A) (hFmeas : ∀ n, MeasurableSet (F n))
    (hmono : Monotone F) (hind : ∀ n, IndepSet A (F n) μ) :
    IndepSet A (⋃ n, F n) μ := by
  have hUnionMeas : MeasurableSet (⋃ n, F n) := MeasurableSet.iUnion hFmeas
  rw [indepSet_iff_measure_inter_eq_mul (μ := μ) hAmeas hUnionMeas]
  have hAFmono : Monotone fun n : ℕ ↦ A ∩ F n := by
    intro n m hnm ω hω
    exact ⟨hω.1, hmono hnm hω.2⟩
  have hAFUnion : (⋃ n : ℕ, A ∩ F n) = A ∩ ⋃ n : ℕ, F n := by
    ext ω
    simp [Set.mem_iUnion]
  have hAFcont : Filter.Tendsto (fun n : ℕ ↦ μ (A ∩ F n)) Filter.atTop
      (nhds (μ (A ∩ ⋃ n : ℕ, F n))) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) hAFmono
    simpa [hAFUnion] using h
  have hFcont : Filter.Tendsto (fun n : ℕ ↦ μ (F n)) Filter.atTop
      (nhds (μ (⋃ n : ℕ, F n))) :=
    tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hA_ne_top : μ A ≠ ∞ := by
    refine ne_of_lt ((measure_mono (Set.subset_univ A)).trans_lt ?_)
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top
  have hprodcont : Filter.Tendsto (fun n : ℕ ↦ μ A * μ (F n)) Filter.atTop
      (nhds (μ A * μ (⋃ n : ℕ, F n))) :=
    ENNReal.Tendsto.const_mul hFcont (Or.inr hA_ne_top)
  have hAFcont' : Filter.Tendsto (fun n : ℕ ↦ μ A * μ (F n)) Filter.atTop
      (nhds (μ (A ∩ ⋃ n : ℕ, F n))) := by
    simpa [funext fun n ↦ (hind n).measure_inter_eq_mul] using hAFcont
  exact tendsto_nhds_unique hAFcont' hprodcont

/-- If a finite open-edge event is independent of every finite encoded Peierls window, then it is
independent of the encoded closed-dual-circuit tail. This is the formal passage from finite
`F_{m,M}` windows to Grimmett's countable tail event `F_m`. -/
theorem indepSet_openEdgeSetEvent_encodedOpenDualCircuitTail_of_windows
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (s : Finset (CubicEdge 2)) (circuits : ∀ n, β n → DualCircuit) (N : ℕ)
    (hind : ∀ M : ℕ,
      IndepSet (openEdgeSetEvent 2 s) (encodedOpenDualCircuitWindow circuits N M)
        (bernoulliBondMeasure 2 p)) :
    IndepSet (openEdgeSetEvent 2 s) (encodedOpenDualCircuitTail circuits N)
      (bernoulliBondMeasure 2 p) := by
  haveI : IsProbabilityMeasure (bernoulliBondMeasure 2 p) := by
    dsimp [bernoulliBondMeasure]
    infer_instance
  rw [← iUnion_encodedOpenDualCircuitWindow_eq_tail circuits N]
  exact indepSet_iUnion_of_monotone
    (measurableSet_openEdgeSetEvent 2 s)
    (fun M ↦ measurableSet_encodedOpenDualCircuitWindow circuits N M)
    (encodedOpenDualCircuitWindow_monotone circuits N) hind

/-- Named-event version of the finite-window Peierls estimate. -/
theorem bernoulliBondMeasure_real_encodedOpenDualCircuitWindow_of_encoding_le
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit) (N M : ℕ)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)) :
    (bernoulliBondMeasure 2 p).real (encodedOpenDualCircuitWindow circuits N M) ≤
      ∑ k : Fin M,
        (((N + (k : ℕ)) * selfAvoidingWalkCount 2 (N + (k : ℕ) - 1) : ℕ) : ℝ) *
          (1 - (p : ℝ)) ^ (N + (k : ℕ)) := by
  simpa [encodedOpenDualCircuitWindow] using
    (bernoulliBondMeasure_real_existsOpenDualCircuit_window_of_encoding_le
      (p := p) (circuits := circuits) (N := N) (M := M) hlen encode)

/-- Named-event version of the countable-tail Peierls estimate. -/
theorem bernoulliBondMeasure_real_encodedOpenDualCircuitTail_of_encoding_le
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit) (N : ℕ)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hsumm : Summable fun k : ℕ ↦
      (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
        (1 - (p : ℝ)) ^ (N + k)) :
    (bernoulliBondMeasure 2 p).real (encodedOpenDualCircuitTail circuits N) ≤
      ∑' k : ℕ,
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          (1 - (p : ℝ)) ^ (N + k) := by
  simpa [encodedOpenDualCircuitTail] using
    (bernoulliBondMeasure_real_existsOpenDualCircuit_tail_of_encoding_le
      (p := p) (circuits := circuits) (N := N) hlen encode hsumm)

/-- Box-indexed version of Grimmett's countable-tail Peierls estimate. For each box scale `N`,
the relevant circuit family may depend on `N`, but the same `n * σ(n-1)` majorant controls the
tail. -/
theorem bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail_of_encoding_le
    {β : ℕ → ℕ → Type*} [∀ N n, Fintype (β N n)] (p : I)
    (circuits : ∀ N n, β N n → DualCircuit) (N : ℕ)
    (hlen : ∀ N n (b : β N n), (circuits N n b).length = n)
    (encode : ∀ N n, β N n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hsumm : Summable fun k : ℕ ↦
      (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
        (1 - (p : ℝ)) ^ (N + k)) :
    (bernoulliBondMeasure 2 p).real (boxIndexedOpenDualCircuitTail circuits N) ≤
      ∑' k : ℕ,
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          (1 - (p : ℝ)) ^ (N + k) := by
  letI : ∀ n, Fintype (β N n) := fun n ↦ inferInstance
  simpa [boxIndexedOpenDualCircuitTail] using
    (bernoulliBondMeasure_real_encodedOpenDualCircuitTail_of_encoding_le
      (p := p) (circuits := fun n ↦ circuits N n) (N := N)
      (hlen := hlen N) (encode := encode N) hsumm)

/-- Encoded Peierls closed-dual-circuit tails have vanishing probability whenever
`(1-p) * λ(2) < 1`. The remaining geometric Peierls work is to instantiate `β`, `circuits`, and
`encode` with the actual surrounding dual circuits from Grimmett's proof. -/
theorem tendsto_bernoulliBondMeasure_real_encodedOpenDualCircuitTail
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    Filter.Tendsto
      (fun N : ℕ ↦ (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω})
      Filter.atTop (nhds 0) := by
  let q : ℝ := 1 - (p : ℝ)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr p.2.2
  have htail : Filter.Tendsto
      (fun N : ℕ ↦ ∑' k : ℕ,
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          q ^ (N + k)) Filter.atTop (nhds 0) := by
    have hcrit :=
      tendsto_peierlsCircuitTail_tsum_of_mul_cubicConnectiveConstant_lt_one 2 hq0 h
    simpa [q, Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using hcrit
  have hnonneg : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω} :=
    Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg
  have hle : ∀ᶠ N : ℕ in Filter.atTop,
      (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
        ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω} ≤
      ∑' k : ℕ,
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          q ^ (N + k) := by
    refine Filter.Eventually.of_forall fun N ↦ ?_
    have hsumm : Summable fun k : ℕ ↦
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          q ^ (N + k) := by
      have hall :=
        summable_peierlsCircuitBound_of_mul_cubicConnectiveConstant_lt_one 2 hq0 h
      have hshift : Summable fun k : ℕ ↦
          ((k + N : ℕ) : ℝ) * (selfAvoidingWalkCount 2 (k + N - 1) : ℝ) *
            q ^ (k + N) :=
        (summable_nat_add_iff (f := fun n : ℕ ↦
          (n : ℝ) * (selfAvoidingWalkCount 2 (n - 1) : ℝ) * q ^ n) N).2 hall
      simpa [Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using hshift
    simpa [q] using
      (bernoulliBondMeasure_real_existsOpenDualCircuit_tail_of_encoding_le
        (p := p) (circuits := circuits) (N := N) hlen encode hsumm)
  exact squeeze_zero' hnonneg hle htail

/-- Named-event version of the encoded Peierls tail convergence theorem. -/
theorem tendsto_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_event
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    Filter.Tendsto
      (fun N : ℕ ↦ (bernoulliBondMeasure 2 p).real
        (encodedOpenDualCircuitTail circuits N))
      Filter.atTop (nhds 0) := by
  simpa [encodedOpenDualCircuitTail] using
    tendsto_bernoulliBondMeasure_real_encodedOpenDualCircuitTail p circuits hlen encode h

/-- Box-indexed encoded Peierls tails have vanishing probability whenever
`(1-p) * λ(2) < 1`. This is the analytic estimate for Grimmett's source-shaped events `F_N`,
where the relevant circuit family may depend on the box scale `N`. -/
theorem tendsto_bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail
    {β : ℕ → ℕ → Type*} [∀ N n, Fintype (β N n)] (p : I)
    (circuits : ∀ N n, β N n → DualCircuit)
    (hlen : ∀ N n (b : β N n), (circuits N n b).length = n)
    (encode : ∀ N n, β N n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    Filter.Tendsto
      (fun N : ℕ ↦ (bernoulliBondMeasure 2 p).real
        (boxIndexedOpenDualCircuitTail circuits N))
      Filter.atTop (nhds 0) := by
  let q : ℝ := 1 - (p : ℝ)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr p.2.2
  have htail : Filter.Tendsto
      (fun N : ℕ ↦ ∑' k : ℕ,
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          q ^ (N + k)) Filter.atTop (nhds 0) := by
    have hcrit :=
      tendsto_peierlsCircuitTail_tsum_of_mul_cubicConnectiveConstant_lt_one 2 hq0 h
    simpa [q, Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using hcrit
  have hnonneg : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ (bernoulliBondMeasure 2 p).real (boxIndexedOpenDualCircuitTail circuits N) :=
    Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg
  have hle : ∀ᶠ N : ℕ in Filter.atTop,
      (bernoulliBondMeasure 2 p).real (boxIndexedOpenDualCircuitTail circuits N) ≤
      ∑' k : ℕ,
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          q ^ (N + k) := by
    refine Filter.Eventually.of_forall fun N ↦ ?_
    have hsumm : Summable fun k : ℕ ↦
        (((N + k) * selfAvoidingWalkCount 2 (N + k - 1) : ℕ) : ℝ) *
          q ^ (N + k) := by
      have hall :=
        summable_peierlsCircuitBound_of_mul_cubicConnectiveConstant_lt_one 2 hq0 h
      have hshift : Summable fun k : ℕ ↦
          ((k + N : ℕ) : ℝ) * (selfAvoidingWalkCount 2 (k + N - 1) : ℝ) *
            q ^ (k + N) :=
        (summable_nat_add_iff (f := fun n : ℕ ↦
          (n : ℝ) * (selfAvoidingWalkCount 2 (n - 1) : ℝ) * q ^ n) N).2 hall
      simpa [Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using hshift
    simpa [q] using
      (bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail_of_encoding_le
        (p := p) (circuits := circuits) (N := N) hlen encode hsumm)
  exact squeeze_zero' hnonneg hle htail

/-- Box-indexed Peierls tails eventually have probability strictly below one when
`(1-p) * λ(2) < 1`. -/
theorem eventually_bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail_lt_one
    {β : ℕ → ℕ → Type*} [∀ N n, Fintype (β N n)] (p : I)
    (circuits : ∀ N n, β N n → DualCircuit)
    (hlen : ∀ N n (b : β N n), (circuits N n b).length = n)
    (encode : ∀ N n, β N n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (bernoulliBondMeasure 2 p).real (boxIndexedOpenDualCircuitTail circuits N) < 1 := by
  have htail :=
    tendsto_bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail p circuits hlen encode h
  exact htail.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))

/-- There is a box-indexed Peierls tail cutoff whose probability is strictly below one whenever
`(1-p) * λ(2) < 1`. -/
theorem exists_bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail_lt_one
    {β : ℕ → ℕ → Type*} [∀ N n, Fintype (β N n)] (p : I)
    (circuits : ∀ N n, β N n → DualCircuit)
    (hlen : ∀ N n (b : β N n), (circuits N n b).length = n)
    (encode : ∀ N n, β N n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∃ N : ℕ,
      (bernoulliBondMeasure 2 p).real (boxIndexedOpenDualCircuitTail circuits N) < 1 :=
  (eventually_bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail_lt_one
    p circuits hlen encode h).exists

/-- Encoded Peierls tails eventually have probability strictly below one when
`(1-p) * λ(2) < 1`. This is the formal `F_m` estimate used before the final independence step in
Grimmett's proof. -/
theorem eventually_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (bernoulliBondMeasure 2 p).real (encodedOpenDualCircuitTail circuits N) < 1 := by
  have htail :=
    tendsto_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_event p circuits hlen encode h
  exact htail.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))

/-- There is a Peierls tail cutoff whose probability is strictly below one whenever
`(1-p) * λ(2) < 1`. -/
theorem exists_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∃ N : ℕ,
      (bernoulliBondMeasure 2 p).real (encodedOpenDualCircuitTail circuits N) < 1 :=
  (eventually_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one
    p circuits hlen encode h).exists

/-- Abstract zero-probability form of the Peierls tail conversion. If an event is contained in
every sufficiently-far encoded closed-dual-circuit tail, then it has probability zero whenever
`(1-p) * λ(2) < 1`. The eventual planar separation lemma should provide the subset hypothesis for
the appropriate bad event. -/
theorem bernoulliBondMeasure_real_eq_zero_of_subset_encodedOpenDualCircuitTails
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit) (A : Set (EdgeConfiguration 2))
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hsubset : ∀ N, A ⊆ {ω : EdgeConfiguration 2 |
      ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω})
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    (bernoulliBondMeasure 2 p).real A = 0 := by
  apply le_antisymm
  · have hconst : Filter.Tendsto (fun _ : ℕ ↦ (bernoulliBondMeasure 2 p).real A)
        Filter.atTop (nhds ((bernoulliBondMeasure 2 p).real A)) :=
      tendsto_const_nhds
    have htail :=
      tendsto_bernoulliBondMeasure_real_encodedOpenDualCircuitTail p circuits hlen encode h
    have hle : (fun _ : ℕ ↦ (bernoulliBondMeasure 2 p).real A) ≤ᶠ[Filter.atTop]
        fun N : ℕ ↦ (bernoulliBondMeasure 2 p).real {ω : EdgeConfiguration 2 |
          ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω} := by
      refine Filter.Eventually.of_forall fun N ↦ ?_
      refine measureReal_mono (hsubset N) ?_
      change setBer((Set.univ : Set (CubicEdge 2)), p)
          {ω : EdgeConfiguration 2 |
            ∃ k : ℕ, ∃ b : β (N + k), (circuits (N + k) b).IsOpen ω} ≠ ∞
      refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
      rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top
    simpa using le_of_tendsto_of_tendsto hconst htail hle
  · exact measureReal_nonneg

/-- Named-event version of the Peierls tail zero-probability criterion. -/
theorem bernoulliBondMeasure_real_eq_zero_of_subset_encodedOpenDualCircuitTail
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit) (A : Set (EdgeConfiguration 2))
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hsubset : ∀ N, A ⊆ encodedOpenDualCircuitTail circuits N)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    (bernoulliBondMeasure 2 p).real A = 0 :=
  bernoulliBondMeasure_real_eq_zero_of_subset_encodedOpenDualCircuitTails
    p circuits A hlen encode hsubset h

/-- Probability algebra for Grimmett's `G_m ∧ ¬F_m` step. If `G` is independent of `F`,
`G` has positive probability, and `F` has probability strictly less than one, then
`G ∩ Fᶜ` has positive probability. The later geometric work should instantiate `G` with a finite
open-edge event and `F` with the relevant closed-dual-circuit tail event. -/
theorem bernoulliBondMeasure_real_inter_compl_pos_of_indepSet
    (p : I) {F G : Set (EdgeConfiguration 2)}
    (hFmeas : MeasurableSet F) (hGmeas : MeasurableSet G)
    (hind : IndepSet G F (bernoulliBondMeasure 2 p))
    (hGpos : 0 < (bernoulliBondMeasure 2 p).real G)
    (hFlt : (bernoulliBondMeasure 2 p).real F < 1) :
    0 < (bernoulliBondMeasure 2 p).real (G ∩ Fᶜ) := by
  let μ := bernoulliBondMeasure 2 p
  have hG_ne_top : μ G ≠ ∞ := by
    change setBer((Set.univ : Set (CubicEdge 2)), p) G ≠ ∞
    refine ne_of_lt ((measure_mono (Set.subset_univ G)).trans_lt ?_)
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top
  have h_inter_real : μ.real (G ∩ F) = μ.real G * μ.real F := by
    rw [Measure.real, hind.measure_inter_eq_mul, ENNReal.toReal_mul]
    rfl
  have hdiff : μ.real (G \ (G ∩ F)) = μ.real G - μ.real (G ∩ F) := by
    exact measureReal_diff Set.inter_subset_left (hGmeas.inter hFmeas) hG_ne_top
  have hset : G \ (G ∩ F) = G ∩ Fᶜ := by
    ext ω
    by_cases hωG : ω ∈ G <;> by_cases hωF : ω ∈ F <;> simp [hωG, hωF]
  have hmul_lt : μ.real G * μ.real F < μ.real G := by
    simpa using mul_lt_mul_of_pos_left hFlt hGpos
  rw [← hset, hdiff, h_inter_real]
  linarith

/-- Grimmett's `G_m ∧ ¬F_m` probability step for the named encoded Peierls tails. If a finite
open-edge event is independent of every encoded tail, then for some cutoff it has positive
probability while no encoded closed-dual circuit tail occurs. The remaining geometric work is to
prove the appropriate independence and the implication to an infinite origin cluster. -/
theorem exists_bernoulliBondMeasure_real_openEdgeSetEvent_inter_compl_encodedOpenDualCircuitTail_pos
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (s : Finset (CubicEdge 2)) (hp : 0 < (p : ℝ))
    (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hind : ∀ N : ℕ,
      IndepSet (openEdgeSetEvent 2 s) (encodedOpenDualCircuitTail circuits N)
        (bernoulliBondMeasure 2 p))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∃ N : ℕ, 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 s ∩ (encodedOpenDualCircuitTail circuits N)ᶜ) := by
  rcases exists_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one
    p circuits hlen encode h with ⟨N, hNlt⟩
  refine ⟨N, ?_⟩
  exact bernoulliBondMeasure_real_inter_compl_pos_of_indepSet p
    (measurableSet_encodedOpenDualCircuitTail circuits N)
    (measurableSet_openEdgeSetEvent 2 s) (hind N)
    (bernoulliBondMeasure_real_openEdgeSetEvent_pos 2 p s hp) hNlt

/-- Version of the named-tail `G_m ∧ ¬F_m` bridge with the positivity of `p` derived from the
Peierls hypothesis `(1-p) * λ(2) < 1`. -/
theorem exists_bernoulliBondMeasure_real_openEdgeSetEvent_inter_compl_encodedOpenDualCircuitTail_pos_of_mul_lt_one
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (s : Finset (CubicEdge 2)) (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hind : ∀ N : ℕ,
      IndepSet (openEdgeSetEvent 2 s) (encodedOpenDualCircuitTail circuits N)
        (bernoulliBondMeasure 2 p))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∃ N : ℕ, 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 s ∩ (encodedOpenDualCircuitTail circuits N)ᶜ) :=
  exists_bernoulliBondMeasure_real_openEdgeSetEvent_inter_compl_encodedOpenDualCircuitTail_pos
    p s (unitInterval_pos_of_one_sub_mul_cubicConnectiveConstant_lt_one (by norm_num) p h)
    circuits hlen encode hind h

/-- Grimmett's finite open event `G_N`, represented by the straight coordinate path of length `N`
from the origin in the square lattice. -/
noncomputable def peierlsStraightOpenPathEdges (N : ℕ) : Finset (CubicEdge 2) :=
  walkEdgeFinset (selfAvoidingWalkWalk (straightSelfAvoidingWalk (d := 2) (by norm_num) N))

/-- The straight path used for `G_N` has exactly `N` distinct bonds. -/
theorem peierlsStraightOpenPathEdges_card (N : ℕ) :
    (peierlsStraightOpenPathEdges N).card = N := by
  rw [peierlsStraightOpenPathEdges]
  rw [walkEdgeFinset_card_of_isTrail
    (selfAvoidingWalkWalk_isPath
      (straightSelfAvoidingWalk (d := 2) (by norm_num) N)).isTrail]
  exact selfAvoidingWalkWalk_length _

/-- If all bonds of Grimmett's straight finite path `G_N` are open, then the origin has an open
self-avoiding path of length at least `N`. -/
theorem openEdgeSetEvent_peierlsStraightOpenPathEdges_subset_hasOpenPathOfLengthAtLeast
    (N : ℕ) :
    openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N) ⊆
      {ω : EdgeConfiguration 2 | hasOpenPathOfLengthAtLeast 2 ω N} := by
  intro ω hω
  let steps : SelfAvoidingWalk 2 N := straightSelfAvoidingWalk (d := 2) (by norm_num) N
  let w := selfAvoidingWalkWalk steps
  have hopen : walkIsOpen ω w := by
    change ω ∈ {ω : EdgeConfiguration 2 | walkIsOpen ω w}
    rw [show {ω : EdgeConfiguration 2 | walkIsOpen ω w} =
        {ω : EdgeConfiguration 2 | (peierlsStraightOpenPathEdges N : Set (CubicEdge 2)) ⊆ ω} by
      rw [walkIsOpen_event_eq_openOn_walkEdgeFinset]
      rfl]
    exact hω
  exact hasOpenPathOfLengthExactly_imp_hasOpenPathOfLengthAtLeast
    ⟨cubicEndpointFrom cubicOrigin steps.1.toList, w, selfAvoidingWalkWalk_isPath steps,
      selfAvoidingWalkWalk_length steps, hopen⟩

/-- The Bernoulli probability of Grimmett's straight finite open event `G_N` is `p^N`. -/
theorem bernoulliBondMeasure_real_peierlsStraightOpenPathEdges (p : I) (N : ℕ) :
    (bernoulliBondMeasure 2 p).real (openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N)) =
      (p : ℝ) ^ N := by
  rw [bernoulliBondMeasure_real_openEdgeSetEvent, peierlsStraightOpenPathEdges_card]

/-- Grimmett's `G_N ∩ F_Nᶜ` probability step for the concrete straight finite open event `G_N`.
If the straight event is independent of the encoded closed-dual-circuit tail at every cutoff, then
for some cutoff it has positive probability while no encoded closed dual circuit in the tail occurs. -/
theorem exists_bernoulliBondMeasure_real_peierlsStraightOpenPathEdges_inter_compl_encodedOpenDualCircuitTail_pos_of_mul_lt_one
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hind : ∀ N : ℕ,
      IndepSet (openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N))
        (encodedOpenDualCircuitTail circuits N) (bernoulliBondMeasure 2 p))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∃ N : ℕ, 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N) ∩
        (encodedOpenDualCircuitTail circuits N)ᶜ) := by
  rcases exists_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one
    p circuits hlen encode h with ⟨N, hNlt⟩
  refine ⟨N, ?_⟩
  have hp : 0 < (p : ℝ) :=
    unitInterval_pos_of_one_sub_mul_cubicConnectiveConstant_lt_one (by norm_num) p h
  have hGpos : 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N)) := by
    rw [bernoulliBondMeasure_real_peierlsStraightOpenPathEdges]
    exact pow_pos hp N
  exact bernoulliBondMeasure_real_inter_compl_pos_of_indepSet p
    (measurableSet_encodedOpenDualCircuitTail circuits N)
    (measurableSet_openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N))
    (hind N) hGpos hNlt

/-- The finite edge set of Grimmett's box `B(m)`, used for the event `G_m` in the source proof:
all bonds of `B(m)` are open. -/
noncomputable def peierlsBoxOpenEdges (m : ℕ) : Finset (CubicEdge 2) :=
  squareBoxEdges m

/-- The Bernoulli probability of Grimmett's box event `G_m` is `p` to the number of bonds in
`B(m)`. -/
theorem bernoulliBondMeasure_real_peierlsBoxOpenEdges (p : I) (m : ℕ) :
    (bernoulliBondMeasure 2 p).real (openEdgeSetEvent 2 (peierlsBoxOpenEdges m)) =
      (p : ℝ) ^ (peierlsBoxOpenEdges m).card :=
  bernoulliBondMeasure_real_openEdgeSetEvent 2 p (peierlsBoxOpenEdges m)

/-- Grimmett's `G_m` has positive probability whenever `p > 0`. -/
theorem bernoulliBondMeasure_real_peierlsBoxOpenEdges_pos (p : I) (m : ℕ)
    (hp : 0 < (p : ℝ)) :
    0 < (bernoulliBondMeasure 2 p).real (openEdgeSetEvent 2 (peierlsBoxOpenEdges m)) :=
  bernoulliBondMeasure_real_openEdgeSetEvent_pos 2 p (peierlsBoxOpenEdges m) hp

/-- Source-shaped `G_N ∧ F_Nᶜ` probability bridge for box-indexed Peierls tails. Here the finite
open event is Grimmett's actual box event `G_N`, and the closed-dual-circuit family defining
`F_N` may depend on the same box scale `N`. -/
theorem exists_bernoulliBondMeasure_real_peierlsBoxOpenEdges_inter_compl_boxIndexedOpenDualCircuitTail_pos_of_mul_lt_one
    {β : ℕ → ℕ → Type*} [∀ N n, Fintype (β N n)] (p : I)
    (circuits : ∀ N n, β N n → DualCircuit)
    (hlen : ∀ N n (b : β N n), (circuits N n b).length = n)
    (encode : ∀ N n, β N n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hind : ∀ N : ℕ,
      IndepSet (openEdgeSetEvent 2 (peierlsBoxOpenEdges N))
        (boxIndexedOpenDualCircuitTail circuits N) (bernoulliBondMeasure 2 p))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∃ N : ℕ, 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (boxIndexedOpenDualCircuitTail circuits N)ᶜ) := by
  rcases exists_bernoulliBondMeasure_real_boxIndexedOpenDualCircuitTail_lt_one
    p circuits hlen encode h with ⟨N, hNlt⟩
  refine ⟨N, ?_⟩
  have hp : 0 < (p : ℝ) :=
    unitInterval_pos_of_one_sub_mul_cubicConnectiveConstant_lt_one (by norm_num) p h
  have hGpos : 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (peierlsBoxOpenEdges N)) :=
    bernoulliBondMeasure_real_peierlsBoxOpenEdges_pos p N hp
  exact bernoulliBondMeasure_real_inter_compl_pos_of_indepSet p
    (measurableSet_boxIndexedOpenDualCircuitTail circuits N)
    (measurableSet_openEdgeSetEvent 2 (peierlsBoxOpenEdges N)) (hind N) hGpos hNlt

/-- Under Grimmett's source box event `G_m`, every square-lattice walk staying inside `B(m)` is
open. -/
theorem walkIsOpen_of_mem_openEdgeSetEvent_peierlsBoxOpenEdges_of_support_subset
    {m : ℕ} {u v : SquareVertex} {ω : EdgeConfiguration 2}
    (hω : ω ∈ openEdgeSetEvent 2 (peierlsBoxOpenEdges m)) (w : squareGraph.Walk u v)
    (hbox : ∀ x : SquareVertex, x ∈ w.support → x ∈ squareBoxVertices m) :
    walkIsOpen ω w := by
  simpa [peierlsBoxOpenEdges] using
    walkIsOpen_of_mem_openEdgeSetEvent_squareBoxEdges_of_support_subset hω w hbox

/-- Under Grimmett's box-open event `G_m`, every vertex of `B(m)` has an open connector from the
origin staying inside the box. -/
theorem exists_open_peierlsBoxConnector {m : ℕ} {ω : EdgeConfiguration 2} {x : SquareVertex}
    (hG : ω ∈ openEdgeSetEvent 2 (peierlsBoxOpenEdges m)) (hx : x ∈ squareBoxVertices m) :
    ∃ c : squareGraph.Walk cubicOrigin x,
      (∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m) ∧ walkIsOpen ω c := by
  rcases exists_squareBoxConnector m hx with ⟨c, hcbox⟩
  exact ⟨c, hcbox,
    walkIsOpen_of_mem_openEdgeSetEvent_peierlsBoxOpenEdges_of_support_subset hG c hcbox⟩

/-- Finite connector form of Grimmett's box-open step. If `G_m` occurs, a connector walk from the
origin to `x` stays inside `B(m)`, and an open self-avoiding path from `x` has tail outside
`B(m)`, then the origin has an open self-avoiding path of the same requested length. -/
theorem hasOpenPathOfLengthAtLeast_of_peierlsBoxOpenEdges_append_outside_tail
    {m n : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hG : ω ∈ openEdgeSetEvent 2 (peierlsBoxOpenEdges m))
    (c : squareGraph.Walk cubicOrigin x)
    (hcbox : ∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m)
    (q : squareGraph.Walk x y) (hqpath : q.IsPath) (hqlen : n ≤ q.length)
    (hqopen : walkIsOpen ω q)
    (hqoutside : ∀ z : SquareVertex, z ∈ q.support.tail → z ∉ squareBoxVertices m) :
    hasOpenPathOfLengthAtLeast 2 ω n := by
  let p : squareGraph.Walk cubicOrigin x := (c.toPath : squareGraph.Walk cubicOrigin x)
  have hpopen : walkIsOpen ω p := by
    exact walkIsOpen_toPath c
      (walkIsOpen_of_mem_openEdgeSetEvent_peierlsBoxOpenEdges_of_support_subset hG c hcbox)
  have hpbox : ∀ z : SquareVertex, z ∈ p.support → z ∈ squareBoxVertices m := by
    intro z hz
    exact hcbox z (SimpleGraph.Walk.support_toPath_subset c hz)
  have hdisj : p.support.Disjoint q.support.tail := by
    intro z hzp hzq
    exact hqoutside z hzq (hpbox z hzp)
  have hlen : n ≤ (p.append q).length := by
    rw [SimpleGraph.Walk.length_append]
    omega
  simpa [p] using
    hasOpenPathOfLengthAtLeastFrom_of_append_disjoint_tail
      (d := 2) (ω := ω) (u := cubicOrigin) (v := x) (w := y)
      (p := p) (q := q) (by simp [p])
      hqpath hdisj hlen hpopen hqopen

/-- Infinite version of the finite connector form: if for every length there is an open
self-avoiding path whose tail avoids `B(m)` after an in-box connector, then `G_m` puts the origin
in an infinite open cluster. -/
theorem hasInfiniteOpenCluster_of_peierlsBoxOpenEdges_and_outside_tails
    {m : ℕ} {ω : EdgeConfiguration 2}
    (hG : ω ∈ openEdgeSetEvent 2 (peierlsBoxOpenEdges m))
    (h : ∀ n : ℕ, ∃ x y : SquareVertex, ∃ c : squareGraph.Walk cubicOrigin x,
      ∃ q : squareGraph.Walk x y,
        (∀ z : SquareVertex, z ∈ c.support → z ∈ squareBoxVertices m) ∧
          q.IsPath ∧ n ≤ q.length ∧ walkIsOpen ω q ∧
          ∀ z : SquareVertex, z ∈ q.support.tail → z ∉ squareBoxVertices m) :
    hasInfiniteOpenCluster 2 ω := by
  rw [hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths]
  intro n
  rcases h n with ⟨x, y, c, q, hcbox, hqpath, hqlen, hqopen, hqoutside⟩
  exact hasOpenPathOfLengthAtLeast_of_peierlsBoxOpenEdges_append_outside_tail
    hG c hcbox q hqpath hqlen hqopen hqoutside

/-- Box-vertex form of Grimmett's box-open step. The connector is supplied by the concrete
Manhattan connector inside `B(m)`. -/
theorem hasOpenPathOfLengthAtLeast_of_peierlsBoxOpenEdges_box_vertex_outside_tail
    {m n : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hG : ω ∈ openEdgeSetEvent 2 (peierlsBoxOpenEdges m)) (hx : x ∈ squareBoxVertices m)
    (q : squareGraph.Walk x y) (hqpath : q.IsPath) (hqlen : n ≤ q.length)
    (hqopen : walkIsOpen ω q)
    (hqoutside : ∀ z : SquareVertex, z ∈ q.support.tail → z ∉ squareBoxVertices m) :
    hasOpenPathOfLengthAtLeast 2 ω n := by
  rcases exists_open_peierlsBoxConnector hG hx with ⟨c, hcbox, _hcopen⟩
  exact hasOpenPathOfLengthAtLeast_of_peierlsBoxOpenEdges_append_outside_tail
    hG c hcbox q hqpath hqlen hqopen hqoutside

/-- Infinite box-vertex form: if for every length some box vertex has an open self-avoiding path
whose tail avoids `B(m)`, then the box-open event puts the origin in an infinite open cluster. -/
theorem hasInfiniteOpenCluster_of_peierlsBoxOpenEdges_and_box_vertex_outside_tails
    {m : ℕ} {ω : EdgeConfiguration 2}
    (hG : ω ∈ openEdgeSetEvent 2 (peierlsBoxOpenEdges m))
    (h : ∀ n : ℕ, ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧
      ∃ y : SquareVertex, ∃ q : squareGraph.Walk x y,
        q.IsPath ∧ n ≤ q.length ∧ walkIsOpen ω q ∧
          ∀ z : SquareVertex, z ∈ q.support.tail → z ∉ squareBoxVertices m) :
    hasInfiniteOpenCluster 2 ω := by
  rw [hasInfiniteOpenCluster_iff_hasArbitrarilyLongOpenPaths]
  intro n
  rcases h n with ⟨x, hx, y, q, hqpath, hqlen, hqopen, hqoutside⟩
  exact hasOpenPathOfLengthAtLeast_of_peierlsBoxOpenEdges_box_vertex_outside_tail
    hG hx q hqpath hqlen hqopen hqoutside

/-- The finite-scale version of the box-exit event: some vertex of `B(m)` has an open
self-avoiding path to outside `B(m+n)`. This is the event whose negation produces the finite
closed boundary in Grimmett's Peierls separation argument. -/
def boxReachesOutsideBoxAtScaleEvent (m n : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧
    ∃ y : SquareVertex, y ∉ squareBoxVertices (m + n) ∧
      ∃ q : squareGraph.Walk x y, q.IsPath ∧ walkIsOpen ω q}

@[simp]
theorem mem_boxReachesOutsideBoxAtScaleEvent (m n : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ boxReachesOutsideBoxAtScaleEvent m n ↔
      ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧
        ∃ y : SquareVertex, y ∉ squareBoxVertices (m + n) ∧
          ∃ q : squareGraph.Walk x y, q.IsPath ∧ walkIsOpen ω q :=
  Iff.rfl

/-- Vertices in `B(M)` reachable from `B(m)` by an open walk that stays in `B(M)`. This is the
finite open cluster whose edge boundary is converted to a closed dual circuit in the remaining
planar separation proof. Walks, rather than paths, are used here because reachability is closed
under appending one open edge; paths are recovered with `Walk.toPath` when an exit event is
needed. -/
noncomputable def boxOpenReachableVertices
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset SquareVertex := by
  classical
  exact (squareBoxVertices M).filter fun x : SquareVertex ↦
    ∃ u : SquareVertex, u ∈ squareBoxVertices m ∧
      ∃ w : squareGraph.Walk u x,
        walkIsOpen ω w ∧ ∀ z : SquareVertex, z ∈ w.support → z ∈ squareBoxVertices M

@[simp]
theorem mem_boxOpenReachableVertices (m M : ℕ) (ω : EdgeConfiguration 2)
    (x : SquareVertex) :
    x ∈ boxOpenReachableVertices m M ω ↔
      x ∈ squareBoxVertices M ∧
        ∃ u : SquareVertex, u ∈ squareBoxVertices m ∧
          ∃ w : squareGraph.Walk u x,
            walkIsOpen ω w ∧
              ∀ z : SquareVertex, z ∈ w.support → z ∈ squareBoxVertices M := by
  classical
  simp [boxOpenReachableVertices]

/-- Every seed vertex of `B(m)` is reachable inside any larger box `B(M)`. -/
theorem squareBox_subset_boxOpenReachableVertices {m M : ℕ} {ω : EdgeConfiguration 2}
    (hmM : m ≤ M) :
    (squareBoxVertices m : Set SquareVertex) ⊆ boxOpenReachableVertices m M ω := by
  intro x hx
  change x ∈ boxOpenReachableVertices m M ω
  rw [mem_boxOpenReachableVertices]
  refine ⟨squareBoxVertices_mono hmM hx, x, hx, SimpleGraph.Walk.nil, ?_, ?_⟩
  · intro e he
    simp at he
  · intro z hz
    rw [SimpleGraph.Walk.mem_support_nil_iff] at hz
    simpa [hz] using squareBoxVertices_mono hmM hx

/-- One open edge from a reachable vertex to a vertex still inside the ambient box keeps the new
vertex in the finite open-reachable cluster. -/
theorem boxOpenReachableVertices_step {m M : ℕ} {ω : EdgeConfiguration 2}
    {x y : SquareVertex} (hx : x ∈ boxOpenReachableVertices m M ω)
    (hxy : squareGraph.Adj x y) (hyM : y ∈ squareBoxVertices M)
    (hopen : edgeOpen ω (⟨s(x, y), by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy⟩ : CubicEdge 2)) :
    y ∈ boxOpenReachableVertices m M ω := by
  rw [mem_boxOpenReachableVertices] at hx ⊢
  rcases hx with ⟨hxM, u, hu, w, hwopen, hwsupport⟩
  let step : squareGraph.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
  have hstepopen : walkIsOpen ω step := by
    intro e he
    simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_singleton] at he
    subst he
    simpa [edgeOpen]
  have hstepsupport : ∀ z : SquareVertex, z ∈ step.support → z ∈ squareBoxVertices M := by
    intro z hz
    simp only [step, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hxM
    · rcases hz with rfl | hz
      · exact hyM
      · simp at hz
  refine ⟨hyM, u, hu, w.append step, walkIsOpen_append hwopen hstepopen, ?_⟩
  exact walk_append_support_subset hwsupport hstepsupport

/-- An edge in the finite box from a reachable vertex to a non-reachable vertex is closed. This
is the graph-theoretic boundary fact used before the planar dual circuit is extracted. -/
theorem not_edgeOpen_of_boxOpenReachableVertices_boundary {m M : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hx : x ∈ boxOpenReachableVertices m M ω) (hxy : squareGraph.Adj x y)
    (hyM : y ∈ squareBoxVertices M) (hy : y ∉ boxOpenReachableVertices m M ω) :
    ¬ edgeOpen ω (⟨s(x, y), by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy⟩ : CubicEdge 2) := by
  intro hopen
  exact hy (boxOpenReachableVertices_step hx hxy hyM hopen)

/-- Positive square-lattice bonds in `B(M)` crossing the boundary of the open-reachable cluster
from `B(m)`. This is a finite, oriented version of the primal boundary that later gets transported
to the shifted dual lattice. -/
noncomputable def boxOpenReachableBoundaryPositiveEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset SquarePositiveEdge := by
  classical
  exact (squareBoxPositiveEdges M).filter fun e : SquarePositiveEdge ↦
    (e.base ∈ boxOpenReachableVertices m M ω ∧
        cubicStepFrom e.base (e.axis, true) ∉ boxOpenReachableVertices m M ω) ∨
      (cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω ∧
        e.base ∉ boxOpenReachableVertices m M ω)

@[simp]
theorem mem_boxOpenReachableBoundaryPositiveEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : SquarePositiveEdge) :
    e ∈ boxOpenReachableBoundaryPositiveEdges m M ω ↔
      e ∈ squareBoxPositiveEdges M ∧
        ((e.base ∈ boxOpenReachableVertices m M ω ∧
            cubicStepFrom e.base (e.axis, true) ∉ boxOpenReachableVertices m M ω) ∨
          (cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω ∧
            e.base ∉ boxOpenReachableVertices m M ω)) := by
  classical
  simp [boxOpenReachableBoundaryPositiveEdges]

/-- Every finite-box boundary bond of the open-reachable cluster is closed. -/
theorem not_edgeOpen_of_mem_boxOpenReachableBoundaryPositiveEdges {m M : ℕ}
    {ω : EdgeConfiguration 2} {e : SquarePositiveEdge}
    (he : e ∈ boxOpenReachableBoundaryPositiveEdges m M ω) :
    ¬ edgeOpen ω e.toEdge := by
  rw [mem_boxOpenReachableBoundaryPositiveEdges] at he
  rcases he with ⟨hebox, hboundary⟩
  have hbox := (mem_squareBoxPositiveEdges_iff M e).mp hebox
  rcases e with ⟨base, axis⟩
  rcases hboundary with hboundary | hboundary
  · exact not_edgeOpen_of_boxOpenReachableVertices_boundary hboundary.1
      (cubicGraph_adj_stepFrom base (axis, true)) hbox.2 hboundary.2
  · intro hopen
    have hclosed := not_edgeOpen_of_boxOpenReachableVertices_boundary hboundary.1
      (cubicGraph_adj_stepFrom base (axis, true)).symm hbox.1 hboundary.2
    have hedge :
        (⟨s(cubicStepFrom base (axis, true), base), by
          rw [SimpleGraph.mem_edgeSet]
          exact (cubicGraph_adj_stepFrom base (axis, true)).symm⟩ : CubicEdge 2) =
          (⟨s(base, cubicStepFrom base (axis, true)), by
            rw [SimpleGraph.mem_edgeSet]
            exact cubicGraph_adj_stepFrom base (axis, true)⟩ : CubicEdge 2) := by
      apply Subtype.ext
      exact Sym2.eq_swap
    exact hclosed (by simpa [SquarePositiveEdge.toEdge, hedge] using hopen)

/-- The embedding that sends a positively oriented primal square bond to the shifted-dual bond
that crosses it. This is the finite-boundary version of the square-lattice crossing bijection. -/
noncomputable def squarePositiveEdgeDualCrossingEmbedding :
    SquarePositiveEdge ↪ DualSquareEdge :=
  squarePositiveEdgeEmbedding.trans squareEdgeDualCrossingEquiv.toEmbedding

@[simp]
theorem squarePositiveEdgeDualCrossingEmbedding_apply (e : SquarePositiveEdge) :
    squarePositiveEdgeDualCrossingEmbedding e = squareEdgeDualCrossingEquiv e.toEdge :=
  rfl

/-- The shifted-dual crossing of the positive horizontal primal edge from `(k,0)` to `(k+1,0)`
is exactly Grimmett's positive-axis crossing edge. -/
theorem squarePositiveEdgeDualCrossingEmbedding_positiveXAxis (k : ℕ) :
    squarePositiveEdgeDualCrossingEmbedding
        (⟨squareVertex (k : ℤ) 0, (0 : Fin 2)⟩ : SquarePositiveEdge) =
      dualPositiveXAxisCrossingEdge k := by
  apply Subtype.ext
  simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
    SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
    primalToDualCrossingPositiveEdge_positiveXAxis, dualPositiveXAxisPositiveEdge_toEdge]

@[simp]
theorem squareEdgeDualCrossingEquiv_symm_squarePositiveEdgeDualCrossingEmbedding
    (e : SquarePositiveEdge) :
    squareEdgeDualCrossingEquiv.symm (squarePositiveEdgeDualCrossingEmbedding e) = e.toEdge := by
  simp [squarePositiveEdgeDualCrossingEmbedding, squarePositiveEdgeEmbedding]

/-- The shifted-dual bonds crossing the finite open-reachable boundary. These are the dual bonds
from which the remaining planar step will extract a closed dual circuit. -/
noncomputable def boxOpenReachableBoundaryDualEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset DualSquareEdge :=
  (boxOpenReachableBoundaryPositiveEdges m M ω).map squarePositiveEdgeDualCrossingEmbedding

@[simp]
theorem mem_boxOpenReachableBoundaryDualEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : DualSquareEdge) :
    e ∈ boxOpenReachableBoundaryDualEdges m M ω ↔
      ∃ b : SquarePositiveEdge,
        b ∈ boxOpenReachableBoundaryPositiveEdges m M ω ∧
          squarePositiveEdgeDualCrossingEmbedding b = e := by
  rw [boxOpenReachableBoundaryDualEdges, Finset.mem_map]

/-- Every shifted-dual bond crossing the open-reachable boundary is open in the induced dual
configuration, equivalently the crossed primal bond is closed. -/
theorem edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableBoundaryDualEdges
    {m M : ℕ} {ω : EdgeConfiguration 2} {e : DualSquareEdge}
    (he : e ∈ boxOpenReachableBoundaryDualEdges m M ω) :
    edgeOpen (dualSquareConfiguration ω) e := by
  rw [mem_boxOpenReachableBoundaryDualEdges] at he
  rcases he with ⟨b, hb, rfl⟩
  rw [dualSquareConfiguration_open_iff]
  have hclosed := not_edgeOpen_of_mem_boxOpenReachableBoundaryPositiveEdges hb
  simpa [edgeOpen] using hclosed

/-- Finset-level form: the whole shifted-dual boundary is open in the dual configuration. -/
theorem boxOpenReachableBoundaryDualEdges_subset_dualSquareConfiguration
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    (boxOpenReachableBoundaryDualEdges m M ω : Set DualSquareEdge) ⊆
      dualSquareConfiguration ω := by
  intro e he
  exact edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableBoundaryDualEdges he

/-- If the finite-scale box-exit event fails, then any open-reachable vertex just inside
`B(m+n)` has only closed edges to vertices outside `B(m+n)`. This is the boundary-to-exterior
half of the finite cluster construction before the dual circuit is extracted. -/
theorem not_edgeOpen_of_boxOpenReachableVertices_boundary_to_outside {m n : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (hx : x ∈ boxOpenReachableVertices m (m + n) ω) (hxy : squareGraph.Adj x y)
    (hyout : y ∉ squareBoxVertices (m + n)) :
    ¬ edgeOpen ω (⟨s(x, y), by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy⟩ : CubicEdge 2) := by
  intro hopen
  rw [mem_boxOpenReachableVertices] at hx
  rcases hx with ⟨_hxM, u, hu, w, hwopen, _hwsupport⟩
  let step : squareGraph.Walk x y := SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil
  have hstepopen : walkIsOpen ω step := by
    intro e he
    simp only [step, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_singleton] at he
    subst he
    simpa [edgeOpen]
  let q : squareGraph.Walk u y := (w.append step).toPath
  have hqpath : q.IsPath := (w.append step).toPath.property
  have hqopen : walkIsOpen ω q :=
    walkIsOpen_toPath (w.append step) (walkIsOpen_append hwopen hstepopen)
  exact hno ⟨u, hu, y, hyout, q, hqpath, hqopen⟩

/-- Boundary bonds in the one-step enlarged box `B(M+1)` crossing from the open-reachable
cluster in `B(M)` to its complement. This finite frontier includes both ordinary in-box boundary
bonds and bonds that leave `B(M)`, which are the edges that appear when the finite exit event
fails. -/
noncomputable def boxOpenReachableFrontierPositiveEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset SquarePositiveEdge := by
  classical
  exact (squareBoxPositiveEdges (M + 1)).filter fun e : SquarePositiveEdge ↦
    (e.base ∈ boxOpenReachableVertices m M ω ∧
        cubicStepFrom e.base (e.axis, true) ∉ boxOpenReachableVertices m M ω) ∨
      (cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω ∧
        e.base ∉ boxOpenReachableVertices m M ω)

@[simp]
theorem mem_boxOpenReachableFrontierPositiveEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : SquarePositiveEdge) :
    e ∈ boxOpenReachableFrontierPositiveEdges m M ω ↔
      e ∈ squareBoxPositiveEdges (M + 1) ∧
        ((e.base ∈ boxOpenReachableVertices m M ω ∧
            cubicStepFrom e.base (e.axis, true) ∉ boxOpenReachableVertices m M ω) ∨
          (cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω ∧
            e.base ∉ boxOpenReachableVertices m M ω)) := by
  classical
  simp [boxOpenReachableFrontierPositiveEdges]

/-- The four positively oriented primal bonds around the shifted-dual vertex `z`, listed in
cyclic order: bottom, right, top, left. These are exactly the primal bonds whose shifted-dual
crossing edge is incident to `z`. -/
def squareCellPositiveEdgeList (z : DualSquareVertex) : List SquarePositiveEdge :=
  [⟨z, (0 : Fin 2)⟩,
    ⟨squareVertex (z 0 + 1) (z 1), (1 : Fin 2)⟩,
    ⟨squareVertex (z 0) (z 1 + 1), (0 : Fin 2)⟩,
    ⟨z, (1 : Fin 2)⟩]

/-- The four positive primal bonds around a shifted-dual vertex are distinct. -/
theorem squareCellPositiveEdgeList_nodup (z : DualSquareVertex) :
    (squareCellPositiveEdgeList z).Nodup := by
  simp [squareCellPositiveEdgeList]
  constructor
  · intro h
    have hcoord := congrFun h (1 : Fin 2)
    simp [squareVertex] at hcoord
  · intro h
    have hcoord := congrFun h (0 : Fin 2)
    simp [squareVertex] at hcoord

/-- The finite set of the four positively oriented primal bonds around `z`. -/
noncomputable def squareCellPositiveEdges (z : DualSquareVertex) :
    Finset SquarePositiveEdge := by
  classical
  exact (squareCellPositiveEdgeList z).toFinset

/-- Around the four sides of a square cell, any vertex predicate changes an even number of times.
This is the local parity replacement for the planar "inside/outside" language: as one walks
around a unit square, membership in a set toggles zero, two, or four times. -/
theorem even_countP_squareCellPositiveEdgeList_boundary
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex) :
    Even ((squareCellPositiveEdgeList z).countP
      (fun e : SquarePositiveEdge ↦
        ¬ (P e.base ↔ P (cubicStepFrom e.base (e.axis, true))))) := by
  classical
  let se : SquareVertex := squareVertex (z 0 + 1) (z 1)
  let nw : SquareVertex := squareVertex (z 0) (z 1 + 1)
  let ne : SquareVertex := squareVertex (z 0 + 1) (z 1 + 1)
  have hbottom : cubicStepFrom z ((0 : Fin 2), true) = se := by
    ext i
    fin_cases i <;> simp [se, cubicStepFrom, cubicDirectionIncrement]
  have hright : cubicStepFrom se ((1 : Fin 2), true) = ne := by
    ext i
    fin_cases i <;> simp [se, ne, cubicStepFrom, cubicDirectionIncrement]
  have htop : cubicStepFrom nw ((0 : Fin 2), true) = ne := by
    ext i
    fin_cases i <;> simp [nw, ne, cubicStepFrom, cubicDirectionIncrement]
  have hleft : cubicStepFrom z ((1 : Fin 2), true) = nw := by
    ext i
    fin_cases i <;> simp [nw, cubicStepFrom, cubicDirectionIncrement]
  by_cases hz : P z <;> by_cases hse : P se <;> by_cases hnw : P nw <;>
    by_cases hne : P ne <;>
      simp [squareCellPositiveEdgeList, se, nw, ne, hbottom, hright, htop, hleft,
        hz, hse, hnw, hne] <;>
      exact ⟨2, rfl⟩

/-- Finset version of the four-side parity lemma. -/
theorem even_card_squareCellPositiveEdges_boundary
    (P : SquareVertex → Prop) [DecidablePred P] (z : DualSquareVertex) :
    Even ((squareCellPositiveEdges z).filter
      (fun e : SquarePositiveEdge ↦
        ¬ (P e.base ↔ P (cubicStepFrom e.base (e.axis, true))))).card := by
  classical
  let q : SquarePositiveEdge → Bool := fun e ↦
    decide (¬ (P e.base ↔ P (cubicStepFrom e.base (e.axis, true))))
  have hcount := even_countP_squareCellPositiveEdgeList_boundary P z
  rw [List.countP_eq_length_filter] at hcount
  have hnodup : ((squareCellPositiveEdgeList z).filter q).Nodup :=
    (squareCellPositiveEdgeList_nodup z).filter q
  rw [← List.toFinset_card_of_nodup hnodup] at hcount
  simpa [squareCellPositiveEdges, q, List.toFinset_filter] using hcount

/-- Each of the four cell-side primal bonds crosses a shifted-dual bond incident to the cell's
dual vertex. -/
theorem mem_crossing_of_mem_squareCellPositiveEdges {z : DualSquareVertex}
    {e : SquarePositiveEdge} (he : e ∈ squareCellPositiveEdges z) :
    z ∈ (squarePositiveEdgeDualCrossingEmbedding e : Sym2 DualSquareVertex) := by
  classical
  simp [squareCellPositiveEdges, squareCellPositiveEdgeList] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement]
  · simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement]
    left
    ext i
    fin_cases i <;> simp [squareVertex]
  · simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement]
    left
    ext i
    fin_cases i <;> simp [squareVertex]
  · simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement]

/-- If a shifted-dual crossing of a positive primal bond is incident to `z`, that primal bond is
one of the four cell-side bonds around `z`. -/
theorem mem_squareCellPositiveEdges_of_mem_crossing {z : DualSquareVertex}
    {e : SquarePositiveEdge}
    (hz : z ∈ (squarePositiveEdgeDualCrossingEmbedding e : Sym2 DualSquareVertex)) :
    e ∈ squareCellPositiveEdges z := by
  classical
  rcases e with ⟨x, i⟩
  fin_cases i
  · simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hz
    rcases hz with hz | hz
    · subst z
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]
    · subst z
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]
  · simp [squarePositiveEdgeDualCrossingEmbedding, squareEdgeDualCrossingEquiv,
      SquarePositiveEdge.edgeEquiv_apply, squarePositiveEdgeDualCrossingEquiv,
      primalToDualCrossingPositiveEdge, SquarePositiveEdge.toEdge, squarePerp,
      cubicStepFrom, cubicDirectionIncrement] at hz
    rcases hz with hz | hz
    · subst z
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]
    · subst z
      simp [squareCellPositiveEdges, squareCellPositiveEdgeList]

/-- A positive primal bond is one of the four sides around `z` iff its shifted-dual crossing is
incident to `z`. -/
theorem mem_squareCellPositiveEdges_iff_mem_crossing {z : DualSquareVertex}
    {e : SquarePositiveEdge} :
    e ∈ squareCellPositiveEdges z ↔
      z ∈ (squarePositiveEdgeDualCrossingEmbedding e : Sym2 DualSquareVertex) :=
  ⟨mem_crossing_of_mem_squareCellPositiveEdges, mem_squareCellPositiveEdges_of_mem_crossing⟩

/-- For the open-reachable finite cluster, the one-step enlarged box condition in the frontier
definition follows automatically from the fact that membership changes across the bond. -/
theorem mem_boxOpenReachableFrontierPositiveEdges_iff_boundary
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : SquarePositiveEdge) :
    e ∈ boxOpenReachableFrontierPositiveEdges m M ω ↔
      ((e.base ∈ boxOpenReachableVertices m M ω ∧
          cubicStepFrom e.base (e.axis, true) ∉ boxOpenReachableVertices m M ω) ∨
        (cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω ∧
          e.base ∉ boxOpenReachableVertices m M ω)) := by
  constructor
  · intro he
    exact (mem_boxOpenReachableFrontierPositiveEdges m M ω e).mp he |>.2
  · intro hboundary
    rw [mem_boxOpenReachableFrontierPositiveEdges]
    constructor
    · rw [mem_squareBoxPositiveEdges_iff]
      rcases hboundary with h | h
      · have hbaseM : e.base ∈ squareBoxVertices M :=
          (mem_boxOpenReachableVertices m M ω e.base).mp h.1 |>.1
        have hstepM_succ :
            cubicStepFrom e.base (e.axis, true) ∈ squareBoxVertices (M + 1) :=
          squareBox_adj_mem_succ hbaseM
            (cubicGraph_adj_stepFrom e.base (e.axis, true))
        exact ⟨squareBoxVertices_mono (Nat.le_succ M) hbaseM, hstepM_succ⟩
      · have hstepM :
            cubicStepFrom e.base (e.axis, true) ∈ squareBoxVertices M :=
          (mem_boxOpenReachableVertices m M ω
            (cubicStepFrom e.base (e.axis, true))).mp h.1 |>.1
        have hbaseM_succ : e.base ∈ squareBoxVertices (M + 1) :=
          squareBox_adj_mem_succ hstepM
            (cubicGraph_adj_stepFrom e.base (e.axis, true)).symm
        exact ⟨hbaseM_succ, squareBoxVertices_mono (Nat.le_succ M) hstepM⟩
    · exact hboundary

/-- Frontier positive primal bonds around a fixed shifted-dual vertex. -/
noncomputable def boxOpenReachableFrontierPositiveEdgesAroundDualVertex
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    Finset SquarePositiveEdge := by
  classical
  exact (boxOpenReachableFrontierPositiveEdges m M ω).filter
    fun e : SquarePositiveEdge ↦ e ∈ squareCellPositiveEdges z

/-- The finite frontier has even primal boundary incidence around every shifted-dual vertex. -/
theorem even_card_boxOpenReachableFrontierPositiveEdgesAroundDualVertex
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    Even (boxOpenReachableFrontierPositiveEdgesAroundDualVertex m M ω z).card := by
  classical
  have hlocal := even_card_squareCellPositiveEdges_boundary
    (fun x : SquareVertex ↦ x ∈ boxOpenReachableVertices m M ω) z
  have hfinset :
      boxOpenReachableFrontierPositiveEdgesAroundDualVertex m M ω z =
        (squareCellPositiveEdges z).filter
          (fun e : SquarePositiveEdge ↦
            ¬ (e.base ∈ boxOpenReachableVertices m M ω ↔
              cubicStepFrom e.base (e.axis, true) ∈
                boxOpenReachableVertices m M ω)) := by
    ext e
    change (e ∈ (boxOpenReachableFrontierPositiveEdges m M ω).filter
        (fun e : SquarePositiveEdge ↦ e ∈ squareCellPositiveEdges z)) ↔
      e ∈ (squareCellPositiveEdges z).filter
        (fun e : SquarePositiveEdge ↦
          ¬ (e.base ∈ boxOpenReachableVertices m M ω ↔
            cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω))
    rw [Finset.mem_filter, Finset.mem_filter,
      mem_boxOpenReachableFrontierPositiveEdges_iff_boundary]
    tauto
  rw [hfinset]
  exact hlocal

/-- A walk from a vertex satisfying `P` to a vertex not satisfying `P` contains an edge crossing
from `P` to its complement. This is the finite graph cut lemma used to locate a Peierls frontier
bond on any attempted exit path. -/
theorem exists_boundary_edge_of_walk_leaves {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    {u v : V} (w : G.Walk u v) (hu : P u) (hv : ¬ P v) :
    ∃ x y : V, P x ∧ ¬ P y ∧ G.Adj x y ∧ s(x, y) ∈ w.edges := by
  induction w with
  | nil => exact (hv hu).elim
  | @cons u₀ v₀ w₀ h p ih =>
      by_cases hv₀ : P v₀
      · rcases ih hv₀ hv with ⟨x, y, hx, hy, hxy, hedges⟩
        refine ⟨x, y, hx, hy, hxy, ?_⟩
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr hedges
      · refine ⟨u₀, v₀, hu, hv₀, h, ?_⟩
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl trivial

/-- Discrete one-dimensional boundary lemma: if a predicate holds at `0` and fails at `R`, then
it changes from true to false across some adjacent pair before `R`. -/
theorem exists_nat_true_false_boundary {P : ℕ → Prop} :
    ∀ R : ℕ, P 0 → ¬ P R → ∃ k : ℕ, k < R ∧ P k ∧ ¬ P (k + 1)
  | 0, h0, hR => (hR h0).elim
  | R + 1, h0, hRsucc => by
      classical
      by_cases hR : P R
      · exact ⟨R, Nat.lt_succ_self R, hR, hRsucc⟩
      · rcases exists_nat_true_false_boundary R h0 hR with ⟨k, hk, hPk, hPk_succ⟩
        exact ⟨k, hk.trans (Nat.lt_succ_self R), hPk, hPk_succ⟩

/-- Finite one-dimensional parity lemma: along a finite line, the number of adjacent membership
changes is odd exactly when the endpoint truth values differ. This is the discrete parity core of
the Peierls contour argument, avoiding any reference to topological interiors. -/
theorem odd_card_filter_nat_changes_iff {P : ℕ → Prop} [DecidablePred P] :
    ∀ R : ℕ,
      Odd ((Finset.range R).filter (fun k ↦ ¬ (P k ↔ P (k + 1)))).card ↔
        ((P 0 ∧ ¬ P R) ∨ (¬ P 0 ∧ P R)) := by
  intro R
  induction R with
  | zero =>
      simp
  | succ R ih =>
      have hrange : Finset.range (R + 1) = insert R (Finset.range R) := by
        ext k
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [hrange, Finset.filter_insert]
      by_cases h0 : P 0 <;>
      by_cases hR : P R <;>
      by_cases hRs : P (R + 1) <;>
      simp [h0, hR, hRs, ih, Finset.card_insert_of_notMem, Nat.odd_add_one]

/-- If a predicate starts true and ends false along a finite line, it changes an odd number of
times. This is the parity version of `exists_nat_true_false_boundary`. -/
theorem odd_card_filter_nat_changes_of_true_false {P : ℕ → Prop} [DecidablePred P]
    {R : ℕ} (h0 : P 0) (hR : ¬ P R) :
    Odd ((Finset.range R).filter (fun k ↦ ¬ (P k ↔ P (k + 1)))).card :=
  (odd_card_filter_nat_changes_iff R).mpr (Or.inl ⟨h0, hR⟩)

/-- If a finite pairwise-disjoint union has odd cardinality, then one member of the union has
odd cardinality. This is the finite parity selection step used after decomposing the Peierls
frontier into edge-disjoint dual circuits. -/
theorem exists_odd_card_of_odd_card_biUnion
    {ι α : Type*} [DecidableEq α] (s : Finset ι) (f : ι → Finset α)
    (hdisj : (s : Set ι).PairwiseDisjoint f)
    (hodd : Odd (s.biUnion f).card) :
    ∃ i ∈ s, Odd (f i).card := by
  classical
  rw [Finset.card_biUnion hdisj] at hodd
  have hodd_filter :
      Odd ((s.filter fun i ↦ Odd (f i).card).card) := by
    exact (Finset.odd_sum_iff_odd_card_odd fun i ↦ (f i).card).mp hodd
  have hnonempty : (s.filter fun i ↦ Odd (f i).card).Nonempty := by
    rcases hodd_filter with ⟨k, hk⟩
    exact Finset.card_pos.mp (by rw [hk]; omega)
  rcases hnonempty with ⟨i, hi⟩
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2⟩

/-- An adjacency crossing out of the finite open-reachable cluster determines a positive
frontier bond representing that unoriented edge. -/
theorem exists_mem_boxOpenReachableFrontierPositiveEdges_of_adj {m M : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hx : x ∈ boxOpenReachableVertices m M ω)
    (hy : y ∉ boxOpenReachableVertices m M ω) (hxy : squareGraph.Adj x y) :
    ∃ e : SquarePositiveEdge, e ∈ boxOpenReachableFrontierPositiveEdges m M ω ∧
      e.toEdge = (⟨s(x, y), by
        rw [SimpleGraph.mem_edgeSet]
        exact hxy⟩ : SquareEdge) := by
  have hxM : x ∈ squareBoxVertices M := by
    exact (mem_boxOpenReachableVertices m M ω x).mp hx |>.1
  have hxM_succ : x ∈ squareBoxVertices (M + 1) :=
    squareBoxVertices_mono (Nat.le_succ M) hxM
  have hyM_succ : y ∈ squareBoxVertices (M + 1) := Percolation.squareBox_adj_mem_succ hxM hxy
  rcases (cubicGraph_adj_iff_exists_stepFrom x y).mp hxy with ⟨a, rfl⟩
  rcases a with ⟨axis, b⟩
  cases b
  · let e : SquarePositiveEdge := ⟨cubicStepFrom x (axis, false), axis⟩
    refine ⟨e, ?_, ?_⟩
    · rw [mem_boxOpenReachableFrontierPositiveEdges]
      constructor
      · rw [mem_squareBoxPositiveEdges_iff]
        exact ⟨hyM_succ, by simpa [e, cubicStepFrom_neg_pos] using hxM_succ⟩
      · right
        constructor
        · simpa [e, cubicStepFrom_neg_pos] using hx
        · simpa [e] using hy
    · apply Subtype.ext
      dsimp [e, SquarePositiveEdge.toEdge]
      rw [cubicStepFrom_neg_pos]
      exact Sym2.eq_swap
  · let e : SquarePositiveEdge := ⟨x, axis⟩
    refine ⟨e, ?_, ?_⟩
    · rw [mem_boxOpenReachableFrontierPositiveEdges]
      exact ⟨by
          rw [mem_squareBoxPositiveEdges_iff]
          exact ⟨hxM_succ, hyM_succ⟩,
        Or.inl ⟨hx, hy⟩⟩
    · apply Subtype.ext
      rfl

/-- Any square-lattice walk from the open-reachable cluster to outside the ambient box crosses a
positive frontier bond. This is the finite cut statement behind the later dual-circuit extraction. -/
theorem exists_mem_boxOpenReachableFrontierPositiveEdges_of_walk_to_outside
    {m M : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hx : x ∈ boxOpenReachableVertices m M ω) (hy : y ∉ squareBoxVertices M)
    (w : squareGraph.Walk x y) :
    ∃ e : SquarePositiveEdge, e ∈ boxOpenReachableFrontierPositiveEdges m M ω ∧
      (e.toEdge : Sym2 SquareVertex) ∈ w.edges := by
  have hy_not_reachable : y ∉ boxOpenReachableVertices m M ω := by
    intro hyreach
    exact hy ((mem_boxOpenReachableVertices m M ω y).mp hyreach).1
  rcases exists_boundary_edge_of_walk_leaves
      (P := fun z : SquareVertex ↦ z ∈ boxOpenReachableVertices m M ω)
      w hx hy_not_reachable with
    ⟨u, v, hu, hv, huv, huv_edges⟩
  rcases exists_mem_boxOpenReachableFrontierPositiveEdges_of_adj hu hv huv with
    ⟨e, he, heq⟩
  refine ⟨e, he, ?_⟩
  have hsym : (e.toEdge : Sym2 SquareVertex) = s(u, v) := congrArg Subtype.val heq
  simpa [hsym.symm] using huv_edges

/-- The old in-box boundary is contained in the one-step enlarged frontier. -/
theorem boxOpenReachableBoundaryPositiveEdges_subset_frontier
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    boxOpenReachableBoundaryPositiveEdges m M ω ⊆
      boxOpenReachableFrontierPositiveEdges m M ω := by
  intro e he
  rw [mem_boxOpenReachableBoundaryPositiveEdges] at he
  rw [mem_boxOpenReachableFrontierPositiveEdges]
  rcases he with ⟨hebox, hboundary⟩
  have hbox := (mem_squareBoxPositiveEdges_iff M e).mp hebox
  refine ⟨?_, hboundary⟩
  rw [mem_squareBoxPositiveEdges_iff]
  exact ⟨squareBoxVertices_mono (Nat.le_succ M) hbox.1,
    squareBoxVertices_mono (Nat.le_succ M) hbox.2⟩

/-- Under failure of the finite-scale exit event, every frontier bond crossing out of the
open-reachable cluster is closed. The proof splits according to whether the other endpoint is
still in `B(m+n)` or has just left the finite box. -/
theorem not_edgeOpen_of_mem_boxOpenReachableFrontierPositiveEdges_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {e : SquarePositiveEdge}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (he : e ∈ boxOpenReachableFrontierPositiveEdges m (m + n) ω) :
    ¬ edgeOpen ω e.toEdge := by
  rw [mem_boxOpenReachableFrontierPositiveEdges] at he
  rcases he with ⟨_hebox, hboundary⟩
  rcases e with ⟨base, axis⟩
  rcases hboundary with hboundary | hboundary
  · by_cases hstepM : cubicStepFrom base (axis, true) ∈ squareBoxVertices (m + n)
    · exact not_edgeOpen_of_boxOpenReachableVertices_boundary hboundary.1
        (cubicGraph_adj_stepFrom base (axis, true)) hstepM hboundary.2
    · exact not_edgeOpen_of_boxOpenReachableVertices_boundary_to_outside hno hboundary.1
        (cubicGraph_adj_stepFrom base (axis, true)) hstepM
  · intro hopen
    by_cases hbaseM : base ∈ squareBoxVertices (m + n)
    · have hclosed := not_edgeOpen_of_boxOpenReachableVertices_boundary hboundary.1
        (cubicGraph_adj_stepFrom base (axis, true)).symm hbaseM hboundary.2
      have hedge :
          (⟨s(cubicStepFrom base (axis, true), base), by
            rw [SimpleGraph.mem_edgeSet]
            exact (cubicGraph_adj_stepFrom base (axis, true)).symm⟩ : CubicEdge 2) =
            (⟨s(base, cubicStepFrom base (axis, true)), by
              rw [SimpleGraph.mem_edgeSet]
              exact cubicGraph_adj_stepFrom base (axis, true)⟩ : CubicEdge 2) := by
        apply Subtype.ext
        exact Sym2.eq_swap
      exact hclosed (by simpa [SquarePositiveEdge.toEdge, hedge] using hopen)
    · have hclosed := not_edgeOpen_of_boxOpenReachableVertices_boundary_to_outside hno
        hboundary.1 (cubicGraph_adj_stepFrom base (axis, true)).symm hbaseM
      have hedge :
          (⟨s(cubicStepFrom base (axis, true), base), by
            rw [SimpleGraph.mem_edgeSet]
            exact (cubicGraph_adj_stepFrom base (axis, true)).symm⟩ : CubicEdge 2) =
            (⟨s(base, cubicStepFrom base (axis, true)), by
              rw [SimpleGraph.mem_edgeSet]
              exact cubicGraph_adj_stepFrom base (axis, true)⟩ : CubicEdge 2) := by
        apply Subtype.ext
        exact Sym2.eq_swap
      exact hclosed (by simpa [SquarePositiveEdge.toEdge, hedge] using hopen)

/-- Shifted-dual bonds crossing the one-step enlarged frontier. -/
noncomputable def boxOpenReachableFrontierDualEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset DualSquareEdge :=
  (boxOpenReachableFrontierPositiveEdges m M ω).map squarePositiveEdgeDualCrossingEmbedding

@[simp]
theorem mem_boxOpenReachableFrontierDualEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : DualSquareEdge) :
    e ∈ boxOpenReachableFrontierDualEdges m M ω ↔
      ∃ b : SquarePositiveEdge,
        b ∈ boxOpenReachableFrontierPositiveEdges m M ω ∧
          squarePositiveEdgeDualCrossingEmbedding b = e := by
  rw [boxOpenReachableFrontierDualEdges, Finset.mem_map]

/-- Shifted-dual frontier bonds incident to a fixed shifted-dual vertex. -/
noncomputable def boxOpenReachableFrontierDualEdgesIncident
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    Finset DualSquareEdge := by
  classical
  exact (boxOpenReachableFrontierDualEdges m M ω).filter
    fun e : DualSquareEdge ↦ z ∈ (e : Sym2 DualSquareVertex)

/-- Incident shifted-dual frontier bonds are exactly the dual crossings of the incident primal
frontier bonds around the same cell vertex. -/
theorem boxOpenReachableFrontierDualEdgesIncident_eq_map
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    boxOpenReachableFrontierDualEdgesIncident m M ω z =
      (boxOpenReachableFrontierPositiveEdgesAroundDualVertex m M ω z).map
        squarePositiveEdgeDualCrossingEmbedding := by
  classical
  ext d
  constructor
  · intro hd
    rw [boxOpenReachableFrontierDualEdgesIncident, Finset.mem_filter] at hd
    rcases hd with ⟨hfrontier, hz⟩
    rw [mem_boxOpenReachableFrontierDualEdges] at hfrontier
    rcases hfrontier with ⟨b, hb, hbd⟩
    rw [Finset.mem_map]
    refine ⟨b, ?_, hbd⟩
    rw [boxOpenReachableFrontierPositiveEdgesAroundDualVertex, Finset.mem_filter]
    exact ⟨hb, (mem_squareCellPositiveEdges_iff_mem_crossing).mpr
      (by simpa [hbd] using hz)⟩
  · intro hd
    rw [Finset.mem_map] at hd
    rcases hd with ⟨b, hbfilter, hbd⟩
    rw [boxOpenReachableFrontierPositiveEdgesAroundDualVertex, Finset.mem_filter] at hbfilter
    rcases hbfilter with ⟨hb, hcell⟩
    rw [boxOpenReachableFrontierDualEdgesIncident, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_boxOpenReachableFrontierDualEdges]
      exact ⟨b, hb, hbd⟩
    · simpa [← hbd] using (mem_squareCellPositiveEdges_iff_mem_crossing).mp hcell

/-- The finite shifted-dual frontier has even degree at every shifted-dual vertex. This is the
formal local parity fact behind the standard Peierls statement that the dual boundary decomposes
into circuits. -/
theorem even_card_boxOpenReachableFrontierDualEdgesIncident
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    Even (boxOpenReachableFrontierDualEdgesIncident m M ω z).card := by
  rw [boxOpenReachableFrontierDualEdgesIncident_eq_map]
  simpa using even_card_boxOpenReachableFrontierPositiveEdgesAroundDualVertex m M ω z

/-- The coercion from shifted-dual square-lattice edges to their underlying unordered endpoints,
as an embedding. This lets the finite frontier edge finset be compared directly with mathlib's
`edgeFinset` and `incidenceFinset` for the generated frontier graph. -/
noncomputable def dualSquareEdgeValEmbedding : DualSquareEdge ↪ Sym2 DualSquareVertex where
  toFun := Subtype.val
  inj' := by
    intro a b h
    exact Subtype.ext h

/-- The finite shifted-dual graph whose edges are the enlarged Peierls frontier. This is the graph
from which the remaining planar step must extract a surrounding circuit. -/
noncomputable def boxOpenReachableFrontierDualGraph
    (m M : ℕ) (ω : EdgeConfiguration 2) : SimpleGraph DualSquareVertex :=
  SimpleGraph.fromEdgeSet
    (Subtype.val '' ((boxOpenReachableFrontierDualEdges m M ω : Finset DualSquareEdge) :
      Set DualSquareEdge))

theorem mem_boxOpenReachableFrontierDualGraph_edgeSet_iff
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : Sym2 DualSquareVertex) :
    e ∈ (boxOpenReachableFrontierDualGraph m M ω).edgeSet ↔
      ∃ h : e ∈ dualSquareGraph.edgeSet,
        (⟨e, h⟩ : DualSquareEdge) ∈ boxOpenReachableFrontierDualEdges m M ω := by
  rw [boxOpenReachableFrontierDualGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨himage, _hnotdiag⟩
    rcases himage with ⟨d, hd, rfl⟩
    exact ⟨d.property, hd⟩
  · rintro ⟨he, hfrontier⟩
    exact ⟨⟨⟨e, he⟩, hfrontier, rfl⟩, dualSquareGraph.not_isDiag_of_mem_edgeSet he⟩

/-- The finite frontier graph has a finite edge set. This explicit instance bridge is needed
because `SimpleGraph.fromEdgeSet` does not infer finiteness from the source finset automatically. -/
theorem boxOpenReachableFrontierDualGraph_edgeSet_finite
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    (boxOpenReachableFrontierDualGraph m M ω).edgeSet.Finite := by
  classical
  refine ((boxOpenReachableFrontierDualEdges m M ω).finite_toSet.image Subtype.val).subset ?_
  intro e he
  rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff] at he
  rcases he with ⟨hedual, hfrontier⟩
  exact ⟨⟨e, hedual⟩, hfrontier, rfl⟩

noncomputable instance instFintypeBoxOpenReachableFrontierDualGraphEdgeSet
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    Fintype (boxOpenReachableFrontierDualGraph m M ω).edgeSet :=
  (boxOpenReachableFrontierDualGraph_edgeSet_finite m M ω).fintype

noncomputable instance instFintypeBoxOpenReachableFrontierDualGraphNeighborSet
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    Fintype ((boxOpenReachableFrontierDualGraph m M ω).neighborSet z) := by
  classical
  let G := boxOpenReachableFrontierDualGraph m M ω
  have hincfinite : (G.incidenceSet z).Finite :=
    (boxOpenReachableFrontierDualGraph_edgeSet_finite m M ω).subset (G.incidenceSet_subset z)
  letI : Fintype (G.incidenceSet z) := hincfinite.fintype
  exact Fintype.ofEquiv (G.incidenceSet z) (G.incidenceSetEquivNeighborSet z)

/-- The generated frontier graph has exactly the unordered endpoints of the finite shifted-dual
frontier finset as its `edgeFinset`. -/
theorem boxOpenReachableFrontierDualGraph_edgeFinset_eq_map
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    (boxOpenReachableFrontierDualGraph m M ω).edgeFinset =
      (boxOpenReachableFrontierDualEdges m M ω).map dualSquareEdgeValEmbedding := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  rw [Finset.mem_map]
  rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff]
  constructor
  · intro h
    rcases h with ⟨hedual, hfrontier⟩
    exact ⟨⟨e, hedual⟩, hfrontier, rfl⟩
  · rintro ⟨d, hd, hde⟩
    subst hde
    exact ⟨d.property, hd⟩

/-- Mathlib's incidence finset of the generated frontier graph is the same as the project's
explicit finset of frontier dual edges incident to the vertex. -/
theorem boxOpenReachableFrontierDualGraph_incidenceFinset_eq_map
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    (boxOpenReachableFrontierDualGraph m M ω).incidenceFinset z =
      (boxOpenReachableFrontierDualEdgesIncident m M ω z).map
        dualSquareEdgeValEmbedding := by
  classical
  rw [SimpleGraph.incidenceFinset_eq_filter]
  rw [boxOpenReachableFrontierDualGraph_edgeFinset_eq_map]
  ext e
  rw [Finset.mem_filter]
  rw [Finset.mem_map]
  rw [Finset.mem_map]
  rw [boxOpenReachableFrontierDualEdgesIncident]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨d, hd, hde⟩, hz⟩
    subst hde
    exact ⟨d, ⟨hd, hz⟩, rfl⟩
  · rintro ⟨d, ⟨hd, hz⟩, hde⟩
    subst hde
    exact ⟨⟨d, hd, rfl⟩, hz⟩

/-- The degree of a vertex in the generated frontier graph is the cardinality of the explicit
incident frontier-edge finset. -/
theorem boxOpenReachableFrontierDualGraph_degree_eq_card_incident
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    (boxOpenReachableFrontierDualGraph m M ω).degree z =
      (boxOpenReachableFrontierDualEdgesIncident m M ω z).card := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  rw [boxOpenReachableFrontierDualGraph_incidenceFinset_eq_map]
  rw [Finset.card_map]

/-- The finite shifted-dual frontier graph has even degree at every shifted-dual vertex. This is
the graph-theoretic version of the local parity lemma and is the main input for the remaining
finite cycle-decomposition step. -/
theorem even_degree_boxOpenReachableFrontierDualGraph
    (m M : ℕ) (ω : EdgeConfiguration 2) (z : DualSquareVertex) :
    Even ((boxOpenReachableFrontierDualGraph m M ω).degree z) := by
  rw [boxOpenReachableFrontierDualGraph_degree_eq_card_incident]
  exact even_card_boxOpenReachableFrontierDualEdgesIncident m M ω z

/-- The shifted-dual frontier graph has finite vertex support. -/
theorem boxOpenReachableFrontierDualGraph_support_finite
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    (boxOpenReachableFrontierDualGraph m M ω).support.Finite :=
  SimpleGraph.support_finite_of_edgeSet_finite
    (boxOpenReachableFrontierDualGraph_edgeSet_finite m M ω)

/-- Every edge of the finite shifted-dual frontier graph is non-bridging. Equivalently, adjacent
frontier vertices are `2`-edge-reachable. This is the graph-theoretic extraction step supplied by
the parity frontier: all degrees are even, so a bridge would create a finite component with exactly
one odd-degree vertex. -/
theorem boxOpenReachableFrontierDualGraph_isEdgeReachable_two_of_adj
    {m M : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (huv : (boxOpenReachableFrontierDualGraph m M ω).Adj u v) :
    (boxOpenReachableFrontierDualGraph m M ω).IsEdgeReachable 2 u v :=
  SimpleGraph.isEdgeReachable_two_of_forall_even_degree_of_finite_support
    (boxOpenReachableFrontierDualGraph_support_finite m M ω)
    (even_degree_boxOpenReachableFrontierDualGraph m M ω) huv

/-- The finite frontier graph is a subgraph of the shifted-dual square lattice. -/
theorem boxOpenReachableFrontierDualGraph_le_dualSquareGraph
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    boxOpenReachableFrontierDualGraph m M ω ≤ dualSquareGraph := by
  intro x y hxy
  rw [boxOpenReachableFrontierDualGraph, SimpleGraph.fromEdgeSet_adj] at hxy
  rcases hxy.1 with ⟨d, _hd, hdxy⟩
  have hmem : s(x, y) ∈ dualSquareGraph.edgeSet := by
    simpa [hdxy] using d.property
  simpa [SimpleGraph.mem_edgeSet] using hmem

/-- A walk in the finite frontier graph, viewed as a shifted-dual square-lattice walk. -/
noncomputable def boxOpenReachableFrontierDualGraphWalk {m M : ℕ} {ω : EdgeConfiguration 2}
    {u v : DualSquareVertex} (w : (boxOpenReachableFrontierDualGraph m M ω).Walk u v) :
    dualSquareGraph.Walk u v :=
  w.mapLe (boxOpenReachableFrontierDualGraph_le_dualSquareGraph m M ω)

/-- Viewing a finite-frontier-graph walk in the ambient shifted-dual graph preserves its second
vertex. -/
theorem boxOpenReachableFrontierDualGraphWalk_snd {m M : ℕ} {ω : EdgeConfiguration 2}
    {u v : DualSquareVertex}
    (w : (boxOpenReachableFrontierDualGraph m M ω).Walk u v) :
    (boxOpenReachableFrontierDualGraphWalk w).snd = w.snd := by
  induction w with
  | nil => rfl
  | cons hadj p ih => simp [boxOpenReachableFrontierDualGraphWalk, SimpleGraph.Walk.map_cons]

/-- Every edge of a finite-frontier-graph walk belongs to the shifted-dual frontier finset. -/
theorem walkEdgeFinset_boxOpenReachableFrontierDualGraphWalk_subset
    {m M : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (w : (boxOpenReachableFrontierDualGraph m M ω).Walk u v) :
    (walkEdgeFinset (boxOpenReachableFrontierDualGraphWalk w) : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m M ω := by
  intro e he
  have he_edges :
      (e : Sym2 DualSquareVertex) ∈
        (boxOpenReachableFrontierDualGraphWalk w).edges :=
    (mem_walkEdgeFinset_iff (boxOpenReachableFrontierDualGraphWalk w) e).mp he
  have he_frontier_graph :
      (e : Sym2 DualSquareVertex) ∈
        (boxOpenReachableFrontierDualGraph m M ω).edgeSet := by
    rw [boxOpenReachableFrontierDualGraphWalk,
      SimpleGraph.Walk.edges_mapLe_eq_edges] at he_edges
    exact w.edges_subset_edgeSet he_edges
  rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff] at he_frontier_graph
  rcases he_frontier_graph with ⟨he_dual, he_frontier⟩
  have heq : (⟨(e : Sym2 DualSquareVertex), he_dual⟩ : DualSquareEdge) = e :=
    Subtype.ext rfl
  simpa [heq] using he_frontier

/-- The primal bonds crossed by the shifted-dual frontier. This is the finite primal edge cut
corresponding to the finite dual frontier. -/
noncomputable def boxOpenReachableFrontierPrimalEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset SquareEdge :=
  (boxOpenReachableFrontierDualEdges m M ω).map squareEdgeDualCrossingEquiv.symm.toEmbedding

@[simp]
theorem mem_boxOpenReachableFrontierPrimalEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : SquareEdge) :
    e ∈ boxOpenReachableFrontierPrimalEdges m M ω ↔
      ∃ d : DualSquareEdge, d ∈ boxOpenReachableFrontierDualEdges m M ω ∧
        squareEdgeDualCrossingEquiv.symm d = e := by
  rw [boxOpenReachableFrontierPrimalEdges, Finset.mem_map]
  constructor
  · rintro ⟨d, hd, hde⟩
    exact ⟨d, hd, by simpa using hde⟩
  · rintro ⟨d, hd, hde⟩
    exact ⟨d, hd, by simpa using hde⟩

/-- Positive-bond form of membership in the primal frontier cut. This removes the intermediate
shifted-dual edge from the statement, which is useful for proving local cut properties. -/
theorem mem_boxOpenReachableFrontierPrimalEdges_iff_positive
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : SquareEdge) :
    e ∈ boxOpenReachableFrontierPrimalEdges m M ω ↔
      ∃ b : SquarePositiveEdge, b ∈ boxOpenReachableFrontierPositiveEdges m M ω ∧
        b.toEdge = e := by
  rw [mem_boxOpenReachableFrontierPrimalEdges]
  constructor
  · rintro ⟨d, hd, hde⟩
    rw [mem_boxOpenReachableFrontierDualEdges] at hd
    rcases hd with ⟨b, hb, rfl⟩
    exact ⟨b, hb, by simpa using hde⟩
  · rintro ⟨b, hb, hbe⟩
    refine ⟨squarePositiveEdgeDualCrossingEmbedding b, ?_, ?_⟩
    · rw [mem_boxOpenReachableFrontierDualEdges]
      exact ⟨b, hb, rfl⟩
    · simp [hbe]

/-- Every primal bond in the finite frontier cut lies in the one-step enlarged ambient box. -/
theorem boxOpenReachableFrontierPrimalEdges_subset_squareBoxEdges_succ
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    boxOpenReachableFrontierPrimalEdges m M ω ⊆ squareBoxEdges (M + 1) := by
  intro e he
  rw [mem_boxOpenReachableFrontierPrimalEdges_iff_positive] at he
  rcases he with ⟨b, hb, rfl⟩
  rw [mem_boxOpenReachableFrontierPositiveEdges] at hb
  exact (SquarePositiveEdge.toEdge_mem_squareBoxEdges_iff (M + 1) b).mpr
    ((mem_squareBoxPositiveEdges_iff (M + 1) b).mp hb.1)

/-- A nearest-neighbour edge crossing from the open-reachable set to its complement belongs to the
explicit primal frontier cut. -/
theorem mem_boxOpenReachableFrontierPrimalEdges_of_adj {m M : ℕ}
    {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hx : x ∈ boxOpenReachableVertices m M ω)
    (hy : y ∉ boxOpenReachableVertices m M ω) (hxy : squareGraph.Adj x y) :
    (⟨s(x, y), by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy⟩ : SquareEdge) ∈ boxOpenReachableFrontierPrimalEdges m M ω := by
  rcases exists_mem_boxOpenReachableFrontierPositiveEdges_of_adj hx hy hxy with
    ⟨b, hb, hbe⟩
  rw [mem_boxOpenReachableFrontierPrimalEdges_iff_positive]
  exact ⟨b, hb, hbe⟩

/-- Membership in the primal frontier cut is exactly being a nearest-neighbour bond crossing from
the open-reachable cluster to its complement. -/
theorem mem_boxOpenReachableFrontierPrimalEdges_iff_boundary_adj
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : SquareEdge) :
    e ∈ boxOpenReachableFrontierPrimalEdges m M ω ↔
      ∃ x y : SquareVertex,
        x ∈ boxOpenReachableVertices m M ω ∧
          y ∉ boxOpenReachableVertices m M ω ∧ squareGraph.Adj x y ∧
            (e : Sym2 SquareVertex) = s(x, y) := by
  constructor
  · intro he
    rw [mem_boxOpenReachableFrontierPrimalEdges_iff_positive] at he
    rcases he with ⟨b, hb, rfl⟩
    rw [mem_boxOpenReachableFrontierPositiveEdges] at hb
    rcases hb with ⟨_hbox, hboundary⟩
    rcases hboundary with hboundary | hboundary
    · refine ⟨b.base, cubicStepFrom b.base (b.axis, true), hboundary.1, hboundary.2,
        cubicGraph_adj_stepFrom b.base (b.axis, true), ?_⟩
      rfl
    · refine ⟨cubicStepFrom b.base (b.axis, true), b.base, hboundary.1, hboundary.2,
        (cubicGraph_adj_stepFrom b.base (b.axis, true)).symm, ?_⟩
      exact Sym2.eq_swap
  · rintro ⟨x, y, hx, hy, hxy, heq⟩
    let e' : SquareEdge := ⟨s(x, y), by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy⟩
    have he' : e' ∈ boxOpenReachableFrontierPrimalEdges m M ω :=
      mem_boxOpenReachableFrontierPrimalEdges_of_adj hx hy hxy
    have heq' : e = e' := Subtype.ext heq
    simpa [heq'] using he'

/-- Under failure of the finite-scale box-exit event, every primal bond in the explicit frontier cut
is closed. This is the primal-cut form of Grimmett's finite closed-boundary construction. -/
theorem not_edgeOpen_of_mem_boxOpenReachableFrontierPrimalEdges_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {e : SquareEdge}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (he : e ∈ boxOpenReachableFrontierPrimalEdges m (m + n) ω) :
    ¬ edgeOpen ω e := by
  rw [mem_boxOpenReachableFrontierPrimalEdges_iff_positive] at he
  rcases he with ⟨b, hb, rfl⟩
  exact not_edgeOpen_of_mem_boxOpenReachableFrontierPositiveEdges_of_not_boxReachesOutside
    hno hb

/-- Finset-level closedness of the explicit primal frontier cut under failure of a finite box exit. -/
theorem disjoint_boxOpenReachableFrontierPrimalEdges_configuration_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n) :
    Disjoint ((boxOpenReachableFrontierPrimalEdges m (m + n) ω : Finset (CubicEdge 2)) :
      Set (CubicEdge 2)) ω := by
  rw [Set.disjoint_left]
  intro e he hω
  exact
    not_edgeOpen_of_mem_boxOpenReachableFrontierPrimalEdges_of_not_boxReachesOutside
      hno he hω

/-- Dual version of the finite cut statement: any walk from the open-reachable cluster to outside
the ambient box crosses a primal edge whose shifted-dual crossing lies in the frontier. -/
theorem exists_mem_boxOpenReachableFrontierDualEdges_of_walk_to_outside
    {m M : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hx : x ∈ boxOpenReachableVertices m M ω) (hy : y ∉ squareBoxVertices M)
    (w : squareGraph.Walk x y) :
    ∃ e : DualSquareEdge, e ∈ boxOpenReachableFrontierDualEdges m M ω ∧
      (squareEdgeDualCrossingEquiv.symm e : Sym2 SquareVertex) ∈ w.edges := by
  rcases exists_mem_boxOpenReachableFrontierPositiveEdges_of_walk_to_outside hx hy w with
    ⟨b, hb, hb_edges⟩
  refine ⟨squarePositiveEdgeDualCrossingEmbedding b, ?_, ?_⟩
  · rw [mem_boxOpenReachableFrontierDualEdges]
    exact ⟨b, hb, rfl⟩
  · simpa using hb_edges

/-- Graph-edge version of the finite cut statement: any primal walk from the open-reachable
cluster to outside the ambient box crosses a primal bond dual to an edge of the finite shifted-dual
frontier graph. -/
theorem exists_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_walk_to_outside
    {m M : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hx : x ∈ boxOpenReachableVertices m M ω) (hy : y ∉ squareBoxVertices M)
    (w : squareGraph.Walk x y) :
    ∃ e : Sym2 DualSquareVertex,
      e ∈ (boxOpenReachableFrontierDualGraph m M ω).edgeSet ∧
        ∃ h : e ∈ dualSquareGraph.edgeSet,
          (squareEdgeDualCrossingEquiv.symm (⟨e, h⟩ : DualSquareEdge) :
            Sym2 SquareVertex) ∈ w.edges := by
  rcases exists_mem_boxOpenReachableFrontierDualEdges_of_walk_to_outside hx hy w with
    ⟨d, hd, hd_edges⟩
  refine ⟨(d : Sym2 DualSquareVertex), ?_, ?_⟩
  · rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff]
    exact ⟨d.property, hd⟩
  · exact ⟨d.property, by simpa using hd_edges⟩

/-- Primal-edge version of the finite cut statement: any walk from the open-reachable cluster to
outside the ambient box uses a bond crossed by the shifted-dual frontier. -/
theorem exists_mem_boxOpenReachableFrontierPrimalEdges_of_walk_to_outside
    {m M : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hx : x ∈ boxOpenReachableVertices m M ω) (hy : y ∉ squareBoxVertices M)
    (w : squareGraph.Walk x y) :
    ∃ e : SquareEdge, e ∈ boxOpenReachableFrontierPrimalEdges m M ω ∧
      (e : Sym2 SquareVertex) ∈ w.edges := by
  rcases exists_mem_boxOpenReachableFrontierDualEdges_of_walk_to_outside hx hy w with
    ⟨d, hd, hd_edges⟩
  refine ⟨squareEdgeDualCrossingEquiv.symm d, ?_, ?_⟩
  · rw [mem_boxOpenReachableFrontierPrimalEdges]
    exact ⟨d, hd, rfl⟩
  · simpa using hd_edges

/-- Source-box version of the finite cut statement: any walk from `B(m)` to outside the ambient
box crosses a primal edge whose shifted-dual crossing lies in the frontier. -/
theorem exists_mem_boxOpenReachableFrontierDualEdges_of_box_walk_to_outside
    {m M : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex} (hmM : m ≤ M)
    (hx : x ∈ squareBoxVertices m) (hy : y ∉ squareBoxVertices M)
    (w : squareGraph.Walk x y) :
    ∃ e : DualSquareEdge, e ∈ boxOpenReachableFrontierDualEdges m M ω ∧
      (squareEdgeDualCrossingEquiv.symm e : Sym2 SquareVertex) ∈ w.edges :=
  exists_mem_boxOpenReachableFrontierDualEdges_of_walk_to_outside
    (squareBox_subset_boxOpenReachableVertices (m := m) (M := M) (ω := ω) hmM hx) hy w

/-- Source-box graph-edge version of the finite cut statement: any primal walk from `B(m)` to
outside the ambient box crosses a primal bond dual to an edge of the finite shifted-dual frontier
graph. -/
theorem exists_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_box_walk_to_outside
    {m M : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex} (hmM : m ≤ M)
    (hx : x ∈ squareBoxVertices m) (hy : y ∉ squareBoxVertices M)
    (w : squareGraph.Walk x y) :
    ∃ e : Sym2 DualSquareVertex,
      e ∈ (boxOpenReachableFrontierDualGraph m M ω).edgeSet ∧
        ∃ h : e ∈ dualSquareGraph.edgeSet,
          (squareEdgeDualCrossingEquiv.symm (⟨e, h⟩ : DualSquareEdge) :
            Sym2 SquareVertex) ∈ w.edges :=
  exists_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_walk_to_outside
    (squareBox_subset_boxOpenReachableVertices (m := m) (M := M) (ω := ω) hmM hx) hy w

/-- Source-box primal-edge version of the finite cut statement: any walk from `B(m)` to outside
the ambient box uses a bond crossed by the shifted-dual frontier. -/
theorem exists_mem_boxOpenReachableFrontierPrimalEdges_of_box_walk_to_outside
    {m M : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex} (hmM : m ≤ M)
    (hx : x ∈ squareBoxVertices m) (hy : y ∉ squareBoxVertices M)
    (w : squareGraph.Walk x y) :
    ∃ e : SquareEdge, e ∈ boxOpenReachableFrontierPrimalEdges m M ω ∧
      (e : Sym2 SquareVertex) ∈ w.edges :=
  exists_mem_boxOpenReachableFrontierPrimalEdges_of_walk_to_outside
    (squareBox_subset_boxOpenReachableVertices (m := m) (M := M) (ω := ω) hmM hx) hy w

/-- The enlarged shifted-dual frontier is nonempty. A deterministic horizontal walk from the
origin to just outside `B(m+n)` must cross the finite open-reachable cut. -/
theorem exists_mem_boxOpenReachableFrontierDualEdges
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    ∃ e : DualSquareEdge, e ∈ boxOpenReachableFrontierDualEdges m (m + n) ω := by
  let R : ℕ := m + n + 1
  rcases exists_squareBoxHorizontalPosConnector R R le_rfl with ⟨w, _hwbox⟩
  have hx : (cubicOrigin : SquareVertex) ∈ boxOpenReachableVertices m (m + n) ω :=
    squareBox_subset_boxOpenReachableVertices (m := m) (M := m + n) (ω := ω)
      (Nat.le_add_right m n) (cubicOrigin_mem_squareBoxVertices m)
  have hy : squareVertex (R : ℤ) 0 ∉ squareBoxVertices (m + n) := by
    rw [mem_squareBoxVertices_iff]
    intro h
    rw [Finset.mem_Icc] at h
    omega
  rcases exists_mem_boxOpenReachableFrontierDualEdges_of_walk_to_outside hx hy w with
    ⟨e, he, _hew⟩
  exact ⟨e, he⟩

/-- The enlarged shifted-dual frontier contains a positive-axis crossing edge. Along the positive
x-axis, the open-reachable set starts true at the origin and is false just outside the ambient
box, so a horizontal primal frontier bond crosses the positive ray; its shifted-dual image is
`dualPositiveXAxisCrossingEdge k`. -/
theorem exists_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    ∃ k : ℕ, k < m + n + 1 ∧
      dualPositiveXAxisCrossingEdge k ∈ boxOpenReachableFrontierDualEdges m (m + n) ω := by
  let M : ℕ := m + n
  let R : ℕ := M + 1
  let P : ℕ → Prop := fun k ↦
    squareVertex (k : ℤ) 0 ∈ boxOpenReachableVertices m M ω
  have h0 : P 0 := by
    have horigin :
        (cubicOrigin : SquareVertex) ∈ boxOpenReachableVertices m M ω :=
      squareBox_subset_boxOpenReachableVertices (m := m) (M := M) (ω := ω)
        (by omega) (cubicOrigin_mem_squareBoxVertices m)
    change squareVertex (0 : ℤ) 0 ∈ boxOpenReachableVertices m M ω
    rw [squareVertex_zero_zero]
    exact horigin
  have hR : ¬ P R := by
    intro hreach
    have hbox : squareVertex (R : ℤ) 0 ∈ squareBoxVertices M :=
      (mem_boxOpenReachableVertices m M ω (squareVertex (R : ℤ) 0)).mp hreach |>.1
    rw [mem_squareBoxVertices_iff] at hbox
    rcases hbox with ⟨hx, _hy⟩
    rw [Finset.mem_Icc] at hx
    omega
  rcases exists_nat_true_false_boundary R h0 hR with ⟨k, hkR, hk, hk_succ⟩
  let e : SquarePositiveEdge := ⟨squareVertex (k : ℤ) 0, (0 : Fin 2)⟩
  have hstep_eq :
      cubicStepFrom (squareVertex (k : ℤ) 0) ((0 : Fin 2), true) =
        squareVertex ((k + 1 : ℕ) : ℤ) 0 := by
    ext i
    fin_cases i <;> simp [cubicStepFrom, cubicDirectionIncrement, squareVertex]
  have hbase_box : squareVertex (k : ℤ) 0 ∈ squareBoxVertices (M + 1) := by
    rw [mem_squareBoxVertices_iff]
    constructor <;> rw [Finset.mem_Icc] <;> constructor <;> omega
  have hstep_box :
      cubicStepFrom (squareVertex (k : ℤ) 0) ((0 : Fin 2), true) ∈
        squareBoxVertices (M + 1) := by
    rw [hstep_eq, mem_squareBoxVertices_iff]
    constructor <;> rw [Finset.mem_Icc] <;> constructor <;> omega
  have he_frontier : e ∈ boxOpenReachableFrontierPositiveEdges m M ω := by
    rw [mem_boxOpenReachableFrontierPositiveEdges]
    refine ⟨?_, Or.inl ?_⟩
    · rw [mem_squareBoxPositiveEdges_iff]
      exact ⟨hbase_box, by simpa [e] using hstep_box⟩
    · exact ⟨by simpa [P, e] using hk, by simpa [P, e, hstep_eq] using hk_succ⟩
  refine ⟨k, by simpa [M, R] using hkR, ?_⟩
  rw [mem_boxOpenReachableFrontierDualEdges]
  exact ⟨e, he_frontier, by
    simpa [e] using squarePositiveEdgeDualCrossingEmbedding_positiveXAxis k⟩

/-- The positive-axis indices where membership in the finite open-reachable set changes. This is
the finite parity count corresponding to the total number of shifted-dual frontier crossings of
the positive horizontal ray. -/
noncomputable def positiveXAxisOpenReachableChangeIndices
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset ℕ := by
  classical
  exact (Finset.range (M + 1)).filter fun k : ℕ ↦
    ¬ (squareVertex (k : ℤ) 0 ∈ boxOpenReachableVertices m M ω ↔
      squareVertex ((k + 1 : ℕ) : ℤ) 0 ∈ boxOpenReachableVertices m M ω)

/-- Along the positive horizontal axis, the finite open-reachable set starts true at the origin
and is false just outside `B(m+n)`, so the number of finite-axis membership changes is odd. This
is the formal version of the parity sentence in the Peierls proof before decomposing the dual
frontier into circuits. -/
theorem positiveXAxisOpenReachableChangeIndices_odd
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    Odd (positiveXAxisOpenReachableChangeIndices m (m + n) ω).card := by
  classical
  let M : ℕ := m + n
  let P : ℕ → Prop := fun k ↦
    squareVertex (k : ℤ) 0 ∈ boxOpenReachableVertices m M ω
  have h0 : P 0 := by
    have horigin :
        (cubicOrigin : SquareVertex) ∈ boxOpenReachableVertices m M ω :=
      squareBox_subset_boxOpenReachableVertices (m := m) (M := M) (ω := ω)
        (by omega) (cubicOrigin_mem_squareBoxVertices m)
    change squareVertex (0 : ℤ) 0 ∈ boxOpenReachableVertices m M ω
    rw [squareVertex_zero_zero]
    exact horigin
  have hR : ¬ P (M + 1) := by
    intro hreach
    have hbox : squareVertex ((M + 1 : ℕ) : ℤ) 0 ∈ squareBoxVertices M :=
      (mem_boxOpenReachableVertices m M ω (squareVertex ((M + 1 : ℕ) : ℤ) 0)).mp
        hreach |>.1
    rw [mem_squareBoxVertices_iff] at hbox
    rcases hbox with ⟨hx, _hy⟩
    rw [Finset.mem_Icc] at hx
    omega
  simpa [positiveXAxisOpenReachableChangeIndices, P, M] using
    odd_card_filter_nat_changes_of_true_false (P := P) h0 hR

/-- Each positive-axis membership change is represented by the corresponding shifted-dual
positive-axis frontier edge. This turns the one-dimensional odd-change count into actual finite
frontier edges. -/
theorem dualPositiveXAxisCrossingEdge_mem_frontier_of_mem_positiveXAxisOpenReachableChangeIndices
    {m M k : ℕ} {ω : EdgeConfiguration 2}
    (hk : k ∈ positiveXAxisOpenReachableChangeIndices m M ω) :
    dualPositiveXAxisCrossingEdge k ∈ boxOpenReachableFrontierDualEdges m M ω := by
  classical
  rw [positiveXAxisOpenReachableChangeIndices, Finset.mem_filter] at hk
  rcases hk with ⟨hk_range, hchange⟩
  let e : SquarePositiveEdge := ⟨squareVertex (k : ℤ) 0, (0 : Fin 2)⟩
  have hstep_eq :
      cubicStepFrom (squareVertex (k : ℤ) 0) ((0 : Fin 2), true) =
        squareVertex ((k + 1 : ℕ) : ℤ) 0 := by
    ext i
    fin_cases i <;> simp [cubicStepFrom, cubicDirectionIncrement, squareVertex]
  have hbase_box : squareVertex (k : ℤ) 0 ∈ squareBoxVertices (M + 1) := by
    rw [mem_squareBoxVertices_iff]
    rw [Finset.mem_range] at hk_range
    constructor <;> rw [Finset.mem_Icc] <;> constructor <;> omega
  have hstep_box :
      cubicStepFrom (squareVertex (k : ℤ) 0) ((0 : Fin 2), true) ∈
        squareBoxVertices (M + 1) := by
    rw [hstep_eq, mem_squareBoxVertices_iff]
    rw [Finset.mem_range] at hk_range
    constructor <;> rw [Finset.mem_Icc] <;> constructor <;> omega
  have hboundary :
      (e.base ∈ boxOpenReachableVertices m M ω ∧
          cubicStepFrom e.base (e.axis, true) ∉ boxOpenReachableVertices m M ω) ∨
        (cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω ∧
          e.base ∉ boxOpenReachableVertices m M ω) := by
    by_cases hbase : squareVertex (k : ℤ) 0 ∈ boxOpenReachableVertices m M ω
    · have hstep : squareVertex ((k + 1 : ℕ) : ℤ) 0 ∉
          boxOpenReachableVertices m M ω := by
        intro hstep
        exact hchange ⟨fun _ ↦ hstep, fun _ ↦ hbase⟩
      exact Or.inl ⟨by simpa [e] using hbase, by simpa [e, hstep_eq] using hstep⟩
    · have hstep : squareVertex ((k + 1 : ℕ) : ℤ) 0 ∈
          boxOpenReachableVertices m M ω := by
        by_contra hstep
        exact hchange ⟨fun h ↦ (hbase h).elim, fun h ↦ (hstep h).elim⟩
      exact Or.inr ⟨by simpa [e, hstep_eq] using hstep, by simpa [e] using hbase⟩
  have he_frontier : e ∈ boxOpenReachableFrontierPositiveEdges m M ω := by
    rw [mem_boxOpenReachableFrontierPositiveEdges]
    refine ⟨?_, hboundary⟩
    rw [mem_squareBoxPositiveEdges_iff]
    exact ⟨hbase_box, by simpa [e] using hstep_box⟩
  rw [mem_boxOpenReachableFrontierDualEdges]
  exact ⟨e, he_frontier, by
    simpa [e] using squarePositiveEdgeDualCrossingEmbedding_positiveXAxis k⟩

/-- The positive-axis crossing edge as an embedding of the coordinate `k`. -/
def dualPositiveXAxisCrossingEdgeEmbedding : ℕ ↪ DualSquareEdge where
  toFun := dualPositiveXAxisCrossingEdge
  inj' := dualPositiveXAxisCrossingEdge_injective

/-- Conversely, if the shifted-dual positive-axis edge at `k` belongs to the finite frontier, then
the finite open-reachable set changes across the corresponding primal positive-axis bond. -/
theorem mem_positiveXAxisOpenReachableChangeIndices_of_dualPositiveXAxisCrossingEdge_mem_frontier
    {m M k : ℕ} {ω : EdgeConfiguration 2}
    (hmem : dualPositiveXAxisCrossingEdge k ∈ boxOpenReachableFrontierDualEdges m M ω) :
    k ∈ positiveXAxisOpenReachableChangeIndices m M ω := by
  classical
  rw [mem_boxOpenReachableFrontierDualEdges] at hmem
  rcases hmem with ⟨b, hb, hbe⟩
  let e : SquarePositiveEdge := ⟨squareVertex (k : ℤ) 0, (0 : Fin 2)⟩
  have hb_eq : b = e := by
    apply squarePositiveEdgeDualCrossingEmbedding.injective
    exact hbe.trans (squarePositiveEdgeDualCrossingEmbedding_positiveXAxis k).symm
  subst b
  rw [mem_boxOpenReachableFrontierPositiveEdges] at hb
  rcases hb with ⟨hbox, hboundary⟩
  have hstep_eq :
      cubicStepFrom (squareVertex (k : ℤ) 0) ((0 : Fin 2), true) =
        squareVertex ((k + 1 : ℕ) : ℤ) 0 := by
    ext i
    fin_cases i <;> simp [cubicStepFrom, cubicDirectionIncrement, squareVertex]
  have hk_range : k ∈ Finset.range (M + 1) := by
    rw [mem_squareBoxPositiveEdges_iff] at hbox
    have hstep_box :
        cubicStepFrom e.base (e.axis, true) ∈ squareBoxVertices (M + 1) := hbox.2
    have hstep_box' :
        squareVertex ((k + 1 : ℕ) : ℤ) 0 ∈ squareBoxVertices (M + 1) := by
      simpa [e, hstep_eq] using hstep_box
    rw [mem_squareBoxVertices_iff] at hstep_box'
    have hx := hstep_box'.1
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    simp at hx
    omega
  have hchange :
      ¬ (squareVertex (k : ℤ) 0 ∈ boxOpenReachableVertices m M ω ↔
        squareVertex ((k + 1 : ℕ) : ℤ) 0 ∈ boxOpenReachableVertices m M ω) := by
    rcases hboundary with hboundary | hboundary
    · rcases hboundary with ⟨hbase, hstep⟩
      intro hiff
      apply hstep
      have hnext : squareVertex ((k + 1 : ℕ) : ℤ) 0 ∈
          boxOpenReachableVertices m M ω :=
        hiff.mp (by simpa [e] using hbase)
      simpa [e, hstep_eq] using hnext
    · rcases hboundary with ⟨hstep, hbase⟩
      intro hiff
      apply hbase
      have hprev : squareVertex (k : ℤ) 0 ∈ boxOpenReachableVertices m M ω :=
        hiff.mpr (by simpa [e, hstep_eq] using hstep)
      simpa [e] using hprev
  rw [positiveXAxisOpenReachableChangeIndices, Finset.mem_filter]
  exact ⟨hk_range, hchange⟩

/-- The positive-axis frontier edge at `k` is present exactly when the finite open-reachable set
changes across the corresponding primal positive-axis bond. -/
theorem dualPositiveXAxisCrossingEdge_mem_frontier_iff_mem_positiveXAxisOpenReachableChangeIndices
    {m M k : ℕ} {ω : EdgeConfiguration 2} :
    dualPositiveXAxisCrossingEdge k ∈ boxOpenReachableFrontierDualEdges m M ω ↔
      k ∈ positiveXAxisOpenReachableChangeIndices m M ω := by
  exact
    ⟨mem_positiveXAxisOpenReachableChangeIndices_of_dualPositiveXAxisCrossingEdge_mem_frontier,
      dualPositiveXAxisCrossingEdge_mem_frontier_of_mem_positiveXAxisOpenReachableChangeIndices⟩

/-- Positive horizontal ray crossing edges in the finite shifted-dual frontier. This is the
frontier-level crossing finset whose parity is computed by the one-dimensional change lemma. -/
noncomputable def boxOpenReachableFrontierPositiveXAxisCrossingEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) : Finset DualSquareEdge := by
  classical
  exact (boxOpenReachableFrontierDualEdges m M ω).filter fun e : DualSquareEdge ↦
    ∃ k : ℕ, e = dualPositiveXAxisCrossingEdge k

@[simp]
theorem mem_boxOpenReachableFrontierPositiveXAxisCrossingEdges
    (m M : ℕ) (ω : EdgeConfiguration 2) (e : DualSquareEdge) :
    e ∈ boxOpenReachableFrontierPositiveXAxisCrossingEdges m M ω ↔
      e ∈ boxOpenReachableFrontierDualEdges m M ω ∧
        ∃ k : ℕ, e = dualPositiveXAxisCrossingEdge k := by
  classical
  simp [boxOpenReachableFrontierPositiveXAxisCrossingEdges]

/-- The positive-axis crossing finset of the finite frontier is exactly the image of the
one-dimensional membership-change indices along the positive primal axis. -/
theorem boxOpenReachableFrontierPositiveXAxisCrossingEdges_eq_map_changes
    (m M : ℕ) (ω : EdgeConfiguration 2) :
    boxOpenReachableFrontierPositiveXAxisCrossingEdges m M ω =
      (positiveXAxisOpenReachableChangeIndices m M ω).map
        dualPositiveXAxisCrossingEdgeEmbedding := by
  classical
  ext e
  rw [mem_boxOpenReachableFrontierPositiveXAxisCrossingEdges, Finset.mem_map]
  constructor
  · rintro ⟨hfrontier, k, rfl⟩
    exact ⟨k,
      (dualPositiveXAxisCrossingEdge_mem_frontier_iff_mem_positiveXAxisOpenReachableChangeIndices).mp
        hfrontier,
      rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact
      ⟨(dualPositiveXAxisCrossingEdge_mem_frontier_iff_mem_positiveXAxisOpenReachableChangeIndices).mpr
          hk,
        ⟨k, rfl⟩⟩

/-- The finite shifted-dual frontier crosses the positive horizontal ray an odd number of times.
This is the event-level parity statement in Grimmett's Peierls contour construction, expressed
without using topological interiors. -/
theorem boxOpenReachableFrontierPositiveXAxisCrossingEdges_odd
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    Odd (boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω).card := by
  rw [boxOpenReachableFrontierPositiveXAxisCrossingEdges_eq_map_changes]
  simpa using positiveXAxisOpenReachableChangeIndices_odd m n ω

/-- If the positive-axis crossings of the finite shifted-dual frontier are decomposed into
edge-disjoint finite pieces, at least one piece has odd crossing number. This is the component
selection step used after decomposing the frontier into dual circuits. -/
theorem exists_odd_card_of_frontierPositiveXAxisCrossingEdges_decomposition
    {ι : Type*} (m n : ℕ) (ω : EdgeConfiguration 2)
    (s : Finset ι) (f : ι → Finset DualSquareEdge)
    (hdisj : (s : Set ι).PairwiseDisjoint f)
    (hcover :
      s.biUnion f = boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω) :
    ∃ i ∈ s, Odd (f i).card := by
  apply exists_odd_card_of_odd_card_biUnion s f hdisj
  rw [hcover]
  exact boxOpenReachableFrontierPositiveXAxisCrossingEdges_odd m n ω

/-- Graph-adjacency form of `exists_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges`.
The positive-axis frontier bond is an edge of the finite shifted-dual frontier graph. -/
theorem exists_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    ∃ k : ℕ, k < m + n + 1 ∧
      (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k) := by
  rcases exists_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges
      m n ω with ⟨k, hk, hmem⟩
  refine ⟨k, hk, ?_⟩
  rw [← SimpleGraph.mem_edgeSet]
  rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff]
  exact ⟨(dualPositiveXAxisCrossingEdge k).property, by
    simpa [dualPositiveXAxisCrossingEdge_coe] using hmem⟩

/-- A positive frontier bond cannot be one of the bonds of the inner box `B(m)`, since every
vertex of `B(m)` is already in the open-reachable cluster. This is the local support-disjointness
fact behind Grimmett's independence of `G_m` from the surrounding closed dual circuit. -/
theorem not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierPositiveEdges
    {m M : ℕ} {ω : EdgeConfiguration 2} {e : SquarePositiveEdge} (hmM : m ≤ M)
    (he : e ∈ boxOpenReachableFrontierPositiveEdges m M ω) :
    e.toEdge ∉ peierlsBoxOpenEdges m := by
  intro hbox
  rw [peierlsBoxOpenEdges, SquarePositiveEdge.toEdge_mem_squareBoxEdges_iff] at hbox
  have hbase : e.base ∈ boxOpenReachableVertices m M ω :=
    squareBox_subset_boxOpenReachableVertices (m := m) (M := M) (ω := ω) hmM hbox.1
  have hstep : cubicStepFrom e.base (e.axis, true) ∈ boxOpenReachableVertices m M ω :=
    squareBox_subset_boxOpenReachableVertices (m := m) (M := M) (ω := ω) hmM hbox.2
  rw [mem_boxOpenReachableFrontierPositiveEdges] at he
  rcases he with ⟨_hebox, hboundary⟩
  rcases hboundary with hboundary | hboundary
  · exact hboundary.2 hstep
  · exact hboundary.2 hbase

/-- A shifted-dual frontier bond crosses no bond of the inner box `B(m)`. -/
theorem not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierDualEdges
    {m M : ℕ} {ω : EdgeConfiguration 2} {e : DualSquareEdge} (hmM : m ≤ M)
    (he : e ∈ boxOpenReachableFrontierDualEdges m M ω) :
    squareEdgeDualCrossingEquiv.symm e ∉ peierlsBoxOpenEdges m := by
  rw [mem_boxOpenReachableFrontierDualEdges] at he
  rcases he with ⟨b, hb, rfl⟩
  simpa using
    (not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierPositiveEdges
      (m := m) (M := M) (ω := ω) hmM hb)

/-- The positive horizontal primal bond at coordinate `k` lies in Grimmett's box `B(m)` whenever
`k < m`. -/
theorem positiveXAxisPrimalEdge_mem_peierlsBoxOpenEdges_of_lt {m k : ℕ} (hk : k < m) :
    SquarePositiveEdge.toEdge
      (⟨squareVertex (k : ℤ) 0, (0 : Fin 2)⟩ : SquarePositiveEdge) ∈
        peierlsBoxOpenEdges m := by
  have hstep_eq :
      cubicStepFrom (squareVertex (k : ℤ) 0) ((0 : Fin 2), true) =
        squareVertex ((k + 1 : ℕ) : ℤ) 0 := by
    ext i
    fin_cases i <;> simp [cubicStepFrom, cubicDirectionIncrement, squareVertex]
  rw [peierlsBoxOpenEdges, SquarePositiveEdge.toEdge_mem_squareBoxEdges_iff]
  constructor
  · rw [mem_squareBoxVertices_iff]
    constructor <;> rw [Finset.mem_Icc] <;> constructor <;> omega
  · rw [hstep_eq, mem_squareBoxVertices_iff]
    constructor <;> rw [Finset.mem_Icc] <;> constructor <;> omega

/-- A positive-axis shifted-dual frontier crossing has coordinate at least the source-box radius.
Otherwise the primal bond it crosses would be one of the bonds of `B(m)`, contradicting the
frontier's disjointness from the box-open support. -/
theorem le_of_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges
    {m M k : ℕ} {ω : EdgeConfiguration 2} (hmM : m ≤ M)
    (hmem : dualPositiveXAxisCrossingEdge k ∈ boxOpenReachableFrontierDualEdges m M ω) :
    m ≤ k := by
  by_contra hmk
  have hk : k < m := Nat.lt_of_not_ge hmk
  let e : SquarePositiveEdge := ⟨squareVertex (k : ℤ) 0, (0 : Fin 2)⟩
  have hcross :
      squareEdgeDualCrossingEquiv.symm (dualPositiveXAxisCrossingEdge k) = e.toEdge := by
    rw [← squarePositiveEdgeDualCrossingEmbedding_positiveXAxis k]
    exact squareEdgeDualCrossingEquiv_symm_squarePositiveEdgeDualCrossingEmbedding e
  have hbox :
      squareEdgeDualCrossingEquiv.symm (dualPositiveXAxisCrossingEdge k) ∈
        peierlsBoxOpenEdges m := by
    simpa [hcross, e] using positiveXAxisPrimalEdge_mem_peierlsBoxOpenEdges_of_lt hk
  exact
    not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierDualEdges
      (m := m) (M := M) (ω := ω) hmM hmem hbox

/-- Adjacency form of
`le_of_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges`. -/
theorem le_of_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph
    {m M k : ℕ} {ω : EdgeConfiguration 2} (hmM : m ≤ M)
    (hadj : (boxOpenReachableFrontierDualGraph m M ω).Adj
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k)) :
    m ≤ k := by
  have hedge :
      s(dualPositiveXAxisLowerVertex k, dualPositiveXAxisUpperVertex k) ∈
        (boxOpenReachableFrontierDualGraph m M ω).edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hadj
  rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff] at hedge
  rcases hedge with ⟨_hdual, hfrontier⟩
  exact le_of_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges
    (m := m) (M := M) (ω := ω) hmM (by
      simpa [dualPositiveXAxisCrossingEdge_coe] using hfrontier)

/-- Bounded graph-adjacency form of the positive-axis frontier edge. The first positive-axis
frontier crossing occurs outside the source box but before the one-step enlarged ambient box. -/
theorem exists_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph_between
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    ∃ k : ℕ, m ≤ k ∧ k < m + n + 1 ∧
      (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k) := by
  rcases exists_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph
      m n ω with ⟨k, hk, hadj⟩
  exact ⟨k,
    le_of_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph
      (m := m) (M := m + n) (ω := ω) (k := k) (Nat.le_add_right m n) hadj,
    hk, hadj⟩

/-- The whole shifted-dual frontier crosses no bond of the inner box `B(m)`. This is the
finite-support version of the `G_m`/frontier disjointness statement. -/
theorem disjoint_peierlsBoxOpenEdges_boxOpenReachableFrontierDualEdges_crossedPrimal
    {m M : ℕ} (ω : EdgeConfiguration 2) (hmM : m ≤ M) :
    Disjoint ((peierlsBoxOpenEdges m : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      (((boxOpenReachableFrontierDualEdges m M ω).map
        squareEdgeDualCrossingEquiv.symm.toEmbedding : Finset (CubicEdge 2)) :
          Set (CubicEdge 2)) := by
  rw [Set.disjoint_left]
  intro e hbox hfrontier
  rcases Finset.mem_map.mp hfrontier with ⟨d, hd, hde⟩
  have hnot :=
    not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierDualEdges
      (m := m) (M := M) (ω := ω) hmM hd
  exact hnot (by simpa [← hde] using hbox)

/-- The finite primal edge cut crossed by the shifted-dual frontier is disjoint from the box-open
support `G_m`. -/
theorem disjoint_peierlsBoxOpenEdges_boxOpenReachableFrontierPrimalEdges
    {m M : ℕ} (ω : EdgeConfiguration 2) (hmM : m ≤ M) :
    Disjoint ((peierlsBoxOpenEdges m : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      ((boxOpenReachableFrontierPrimalEdges m M ω : Finset (CubicEdge 2)) :
        Set (CubicEdge 2)) := by
  simpa [boxOpenReachableFrontierPrimalEdges] using
    disjoint_peierlsBoxOpenEdges_boxOpenReachableFrontierDualEdges_crossedPrimal
      (m := m) (M := M) ω hmM

/-- Under failure of the finite-scale exit event, every shifted-dual bond crossing the enlarged
frontier is open in the induced dual configuration. -/
theorem edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {e : DualSquareEdge}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (he : e ∈ boxOpenReachableFrontierDualEdges m (m + n) ω) :
    edgeOpen (dualSquareConfiguration ω) e := by
  rw [mem_boxOpenReachableFrontierDualEdges] at he
  rcases he with ⟨b, hb, rfl⟩
  rw [dualSquareConfiguration_open_iff]
  have hclosed :=
    not_edgeOpen_of_mem_boxOpenReachableFrontierPositiveEdges_of_not_boxReachesOutside hno hb
  simpa [edgeOpen] using hclosed

/-- If the finite box-exit event fails, the enlarged shifted-dual frontier contains at least one
dual-open bond. The remaining Peierls circuit-extraction step must upgrade this nonempty open
frontier cut to a closed shifted-dual circuit surrounding the source box. -/
theorem exists_open_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n) :
    ∃ e : DualSquareEdge,
      e ∈ boxOpenReachableFrontierDualEdges m (m + n) ω ∧
        edgeOpen (dualSquareConfiguration ω) e := by
  rcases exists_mem_boxOpenReachableFrontierDualEdges m n ω with ⟨e, he⟩
  exact ⟨e, he,
    edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside
      hno he⟩

/-- Finset-level form of the enlarged frontier dual-open statement. -/
theorem boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n) :
    (boxOpenReachableFrontierDualEdges m (m + n) ω : Set DualSquareEdge) ⊆
      dualSquareConfiguration ω := by
  intro e he
  exact
    edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside
      hno he

/-- Graph-edge form of frontier dual-openness under failure of a finite box exit. Any edge of the
finite shifted-dual frontier graph is open in the induced dual configuration. -/
theorem edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {e : Sym2 DualSquareVertex}
    {h : e ∈ dualSquareGraph.edgeSet}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (he : e ∈ (boxOpenReachableFrontierDualGraph m (m + n) ω).edgeSet) :
    edgeOpen (dualSquareConfiguration ω) (⟨e, h⟩ : DualSquareEdge) := by
  rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff] at he
  rcases he with ⟨h', hfrontier⟩
  have heq : (⟨e, h⟩ : DualSquareEdge) = ⟨e, h'⟩ := Subtype.ext rfl
  rw [heq]
  exact
    edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside
      hno hfrontier

/-- If the finite box-exit event fails, the finite shifted-dual frontier graph has a dual-open
edge. -/
theorem exists_open_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n) :
    ∃ e : Sym2 DualSquareVertex,
      e ∈ (boxOpenReachableFrontierDualGraph m (m + n) ω).edgeSet ∧
        ∃ h : e ∈ dualSquareGraph.edgeSet,
          edgeOpen (dualSquareConfiguration ω) (⟨e, h⟩ : DualSquareEdge) := by
  rcases exists_mem_boxOpenReachableFrontierDualEdges m n ω with ⟨d, hd⟩
  refine ⟨(d : Sym2 DualSquareVertex), ?_, ?_⟩
  · rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff]
    exact ⟨d.property, hd⟩
  · exact ⟨d.property,
      edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualEdges_of_not_boxReachesOutside
        hno hd⟩

/-- Under failure of a finite box exit, any primal walk from the open-reachable cluster to outside
the ambient box crosses a primal bond whose shifted-dual graph edge is open in the induced dual
configuration. -/
theorem exists_open_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_walk_to_outside_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (hx : x ∈ boxOpenReachableVertices m (m + n) ω)
    (hy : y ∉ squareBoxVertices (m + n)) (w : squareGraph.Walk x y) :
    ∃ e : Sym2 DualSquareVertex,
      e ∈ (boxOpenReachableFrontierDualGraph m (m + n) ω).edgeSet ∧
        ∃ h : e ∈ dualSquareGraph.edgeSet,
          edgeOpen (dualSquareConfiguration ω) (⟨e, h⟩ : DualSquareEdge) ∧
            (squareEdgeDualCrossingEquiv.symm (⟨e, h⟩ : DualSquareEdge) :
              Sym2 SquareVertex) ∈ w.edges := by
  rcases exists_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_walk_to_outside hx hy w with
    ⟨e, he_graph, hcross⟩
  rcases hcross with ⟨hdual, hcross_edges⟩
  refine ⟨e, he_graph, hdual, ?_, hcross_edges⟩
  exact
    edgeOpen_dualSquareConfiguration_of_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_not_boxReachesOutside
      hno he_graph

/-- Source-box version: under failure of a finite box exit, any primal walk from `B(m)` to outside
`B(m+n)` crosses a dual-open edge of the finite shifted-dual frontier graph. -/
theorem exists_open_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_box_walk_to_outside_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {x y : SquareVertex}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (hx : x ∈ squareBoxVertices m) (hy : y ∉ squareBoxVertices (m + n))
    (w : squareGraph.Walk x y) :
    ∃ e : Sym2 DualSquareVertex,
      e ∈ (boxOpenReachableFrontierDualGraph m (m + n) ω).edgeSet ∧
        ∃ h : e ∈ dualSquareGraph.edgeSet,
          edgeOpen (dualSquareConfiguration ω) (⟨e, h⟩ : DualSquareEdge) ∧
            (squareEdgeDualCrossingEquiv.symm (⟨e, h⟩ : DualSquareEdge) :
              Sym2 SquareVertex) ∈ w.edges :=
  exists_open_mem_boxOpenReachableFrontierDualGraph_edgeSet_of_walk_to_outside_of_not_boxReachesOutside
    hno (squareBox_subset_boxOpenReachableVertices (m := m) (M := m + n) (ω := ω)
      (Nat.le_add_right m n) hx) hy w

/-- Every walk in the finite shifted-dual frontier graph is dual-open when the corresponding
finite box-exit event fails. -/
theorem dualWalkIsOpen_boxOpenReachableFrontierDualGraphWalk_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (w : (boxOpenReachableFrontierDualGraph m (m + n) ω).Walk u v) :
    dualWalkIsOpen ω (boxOpenReachableFrontierDualGraphWalk w) := by
  intro e he
  let ed : DualSquareEdge :=
    ⟨e, (boxOpenReachableFrontierDualGraphWalk w).edges_subset_edgeSet he⟩
  have hed : ed ∈ walkEdgeFinset (boxOpenReachableFrontierDualGraphWalk w) :=
    (mem_walkEdgeFinset_iff (boxOpenReachableFrontierDualGraphWalk w) ed).mpr he
  exact boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
    hno (walkEdgeFinset_boxOpenReachableFrontierDualGraphWalk_subset w hed)

/-- A circuit in the finite frontier graph, packaged as a shifted-dual square-lattice circuit. -/
noncomputable def dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit
    {m M : ℕ} {ω : EdgeConfiguration 2} {u : DualSquareVertex}
    (w : (boxOpenReachableFrontierDualGraph m M ω).Walk u u) (hw : w.IsCircuit) :
    DualCircuit where
  vertex := u
  walk := boxOpenReachableFrontierDualGraphWalk w
  isCircuit := by
    refine ⟨?_, ?_⟩
    · exact hw.isTrail.mapLe (boxOpenReachableFrontierDualGraph_le_dualSquareGraph m M ω)
    · intro hnil
      have hNil_mapped : (boxOpenReachableFrontierDualGraphWalk w).Nil :=
        SimpleGraph.Walk.eq_nil_iff_nil.mp hnil
      have hlen_mapped : (boxOpenReachableFrontierDualGraphWalk w).length = 0 :=
        SimpleGraph.Walk.length_eq_zero_iff.mpr hNil_mapped
      have hlen_eq : (boxOpenReachableFrontierDualGraphWalk w).length = w.length := by
        exact SimpleGraph.Walk.length_map
          (f := SimpleGraph.Hom.ofLE
            (boxOpenReachableFrontierDualGraph_le_dualSquareGraph m M ω))
          (p := w)
      have hlen_w : w.length = 0 := by
        exact hlen_eq.symm.trans hlen_mapped
      exact hw.ne_nil (SimpleGraph.Walk.eq_nil_iff_nil.mpr
        (SimpleGraph.Walk.length_eq_zero_iff.mp hlen_w))

@[simp]
theorem dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_length
    {m M : ℕ} {ω : EdgeConfiguration 2} {u : DualSquareVertex}
    (w : (boxOpenReachableFrontierDualGraph m M ω).Walk u u) (hw : w.IsCircuit) :
    (dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw).length = w.length := by
  change (boxOpenReachableFrontierDualGraphWalk w).length = w.length
  exact SimpleGraph.Walk.length_map
    (f := SimpleGraph.Hom.ofLE (boxOpenReachableFrontierDualGraph_le_dualSquareGraph m M ω))
    (p := w)

/-- The shifted-dual circuit obtained from a finite frontier-graph circuit is supported by the
frontier finset. -/
theorem walkEdgeFinset_dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_subset
    {m M : ℕ} {ω : EdgeConfiguration 2} {u : DualSquareVertex}
    (w : (boxOpenReachableFrontierDualGraph m M ω).Walk u u) (hw : w.IsCircuit) :
    (walkEdgeFinset
        (dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw).walk :
          Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m M ω := by
  simpa [dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit] using
    (walkEdgeFinset_boxOpenReachableFrontierDualGraphWalk_subset w)

/-- Under failure of the finite box-exit event, every circuit in the finite frontier graph gives an
open shifted-dual circuit. This is the graph-form bridge needed by the final circuit-extraction
theorem. -/
theorem dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_isOpen_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2} {u : DualSquareVertex}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (w : (boxOpenReachableFrontierDualGraph m (m + n) ω).Walk u u) (hw : w.IsCircuit) :
    (dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw).IsOpen ω := by
  intro e he
  let ed : DualSquareEdge :=
    ⟨e, (dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw).walk.edges_subset_edgeSet he⟩
  have hed : ed ∈ walkEdgeFinset
      (dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw).walk :=
    (mem_walkEdgeFinset_iff
      (dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw).walk ed).mpr he
  exact boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
    hno
    (walkEdgeFinset_dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_subset w hw hed)

/-- The direct output of a finite-box crossing version of the planar no-circuit lemma: from some
vertex of `B(m)` there are open self-avoiding paths reaching outside every larger box
`B(m+n)`. A last-visit trimming lemma converts this into `boxVertexOutsideTailsEvent`. -/
def boxVertexReachesOutsideBoxEvent (m : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∀ n : ℕ, ω ∈ boxReachesOutsideBoxAtScaleEvent m n}

@[simp]
theorem mem_boxVertexReachesOutsideBoxEvent (m : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ boxVertexReachesOutsideBoxEvent m ↔
      ∀ n : ℕ, ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧
        ∃ y : SquareVertex, y ∉ squareBoxVertices (m + n) ∧
          ∃ q : squareGraph.Walk x y, q.IsPath ∧ walkIsOpen ω q :=
  Iff.rfl

/-- The infinite box-exit event is the intersection of its finite-scale box-exit events. -/
theorem mem_boxVertexReachesOutsideBoxEvent_iff_forall_scale (m : ℕ)
    (ω : EdgeConfiguration 2) :
    ω ∈ boxVertexReachesOutsideBoxEvent m ↔
      ∀ n : ℕ, ω ∈ boxReachesOutsideBoxAtScaleEvent m n :=
  Iff.rfl

/-- The direct outside-tail output expected from the planar no-closed-dual-circuit separation
lemma: for every requested length, some vertex of `B(m)` starts an open self-avoiding path whose
tail immediately stays outside `B(m)`. Under the box-open event `G_m`, the origin is connected to
that starting vertex by the concrete Manhattan connector. -/
def boxVertexOutsideTailsEvent (m : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∀ n : ℕ, ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧
    ∃ y : SquareVertex, ∃ q : squareGraph.Walk x y,
      q.IsPath ∧ n ≤ q.length ∧ walkIsOpen ω q ∧
        ∀ z : SquareVertex, z ∈ q.support.tail → z ∉ squareBoxVertices m}

@[simp]
theorem mem_boxVertexOutsideTailsEvent (m : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ boxVertexOutsideTailsEvent m ↔
      ∀ n : ℕ, ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧
        ∃ y : SquareVertex, ∃ q : squareGraph.Walk x y,
          q.IsPath ∧ n ≤ q.length ∧ walkIsOpen ω q ∧
            ∀ z : SquareVertex, z ∈ q.support.tail → z ∉ squareBoxVertices m :=
  Iff.rfl

/-- Last-visit trimming converts open paths from `B(m)` to outside every larger box into the
outside-tail event used by the box-open connector step. -/
theorem boxVertexReachesOutsideBoxEvent_subset_boxVertexOutsideTailsEvent (m : ℕ) :
    boxVertexReachesOutsideBoxEvent m ⊆ boxVertexOutsideTailsEvent m := by
  intro ω hω n
  rcases hω n with ⟨x, hx, y, hy, q, hqpath, hqopen⟩
  have hy_box : y ∉ squareBoxVertices m := by
    intro hy'
    exact hy (squareBoxVertices_mono (Nat.le_add_right m n) hy')
  have hmem : ∃ z : SquareVertex, z ∈ q.support ∧ z ∈ squareBoxVertices m :=
    ⟨x, q.start_mem_support, hx⟩
  rcases exists_isSubwalk_suffix_from_last_region
      (P := fun z : SquareVertex ↦ z ∈ squareBoxVertices m) q hmem hy_box with
    ⟨x', hx', r, hrsub, hroutside⟩
  have hrpath : r.IsPath := walk_isPath_of_isSubwalk hqpath hrsub
  have hropen : walkIsOpen ω r := walkIsOpen_of_isSubwalk hqopen hrsub
  have hrlen : n ≤ r.length := squareBox_exit_walk_length_ge hx' hy r
  exact ⟨x', hx', y, r, hrpath, hrlen, hropen, hroutside⟩

/-- The source box event `G_m` connects the direct outside-tail separation output back to the
origin. This is the event-level form of the concrete connector/path-surgery proof. -/
theorem openBox_inter_boxVertexOutsideTailsEvent_subset_origin_infinite (m : ℕ) :
    openEdgeSetEvent 2 (peierlsBoxOpenEdges m) ∩ boxVertexOutsideTailsEvent m ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω} := by
  intro ω hω
  exact hasInfiniteOpenCluster_of_peierlsBoxOpenEdges_and_box_vertex_outside_tails hω.1 hω.2

/-- If absence of the encoded closed-dual-circuit tail gives the direct outside-tail event from
some box vertex, then Grimmett's source box event `G_m` gives an infinite open cluster at the
origin. -/
theorem openBox_inter_tail_compl_subset_origin_infinite_of_box_vertex_outside_tails
    {β : ℕ → Type*} (circuits : ∀ n, β n → DualCircuit) (N : ℕ)
    (hsep : (encodedOpenDualCircuitTail circuits N)ᶜ ⊆ boxVertexOutsideTailsEvent N) :
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω} := by
  intro ω hω
  exact openBox_inter_boxVertexOutsideTailsEvent_subset_origin_infinite N ⟨hω.1, hsep hω.2⟩

/-- The event that some vertex of Grimmett's box `B(m)` lies in an infinite open cluster. This is
the immediate output of the planar separation lemma before the box-open event connects that vertex
back to the origin. -/
def boxVertexInfiniteOpenClusterEvent (m : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧ hasInfiniteOpenClusterFrom 2 ω x}

@[simp]
theorem mem_boxVertexInfiniteOpenClusterEvent (m : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ boxVertexInfiniteOpenClusterEvent m ↔
      ∃ x : SquareVertex, x ∈ squareBoxVertices m ∧ hasInfiniteOpenClusterFrom 2 ω x :=
  Iff.rfl

/-- If the origin has an infinite open cluster, then every box witnesses the corresponding
box-vertex event. -/
theorem hasInfiniteOpenCluster_subset_boxVertexInfiniteOpenClusterEvent (m : ℕ) :
    {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω} ⊆
      boxVertexInfiniteOpenClusterEvent m := by
  intro ω hω
  exact ⟨cubicOrigin, cubicOrigin_mem_squareBoxVertices m, hω⟩

/-- Combine the two geometric pieces in Grimmett's Peierls separation step: no closed dual circuit
around the box gives an infinite open cluster from some box vertex, and the box-open event connects
that vertex to the origin. -/
theorem openBox_inter_tail_compl_subset_origin_infinite_of_box_vertex
    {β : ℕ → Type*} (circuits : ∀ n, β n → DualCircuit) (N : ℕ)
    (hsep : (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      boxVertexInfiniteOpenClusterEvent N)
    (hconnect : openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        boxVertexInfiniteOpenClusterEvent N ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}) :
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω} := by
  intro ω hω
  exact hconnect ⟨hω.1, hsep hω.2⟩

namespace DualCircuit

/-- A shifted-dual circuit avoids Grimmett's box event `G_N` if the primal bonds it crosses are
disjoint from the bonds of `B(N)`. For circuits surrounding `B(N)`, this is the concrete geometric
fact needed to obtain finite-window independence from the box-open event. -/
def AvoidsBoxEdges (N : ℕ) (c : DualCircuit) : Prop :=
  Disjoint ((peierlsBoxOpenEdges N : Finset (CubicEdge 2)) : Set (CubicEdge 2))
    ((c.crossedPrimalEdgeFinset : Finset (CubicEdge 2)) : Set (CubicEdge 2))

/-- A circuit supported by the finite shifted-dual frontier crosses no bond of the inner box. -/
theorem avoidsBoxEdges_of_walkEdgeFinset_subset_boxOpenReachableFrontierDualEdges
    {m M : ℕ} {ω : EdgeConfiguration 2} {c : DualCircuit} (hmM : m ≤ M)
    (hsubset :
      (walkEdgeFinset c.walk : Set DualSquareEdge) ⊆
        boxOpenReachableFrontierDualEdges m M ω) :
    c.AvoidsBoxEdges m := by
  rw [AvoidsBoxEdges]
  rw [Set.disjoint_left]
  intro e hebox hec
  rw [crossedPrimalEdgeFinset] at hec
  rcases Finset.mem_map.mp hec with ⟨ed, hed, rfl⟩
  exact not_mem_peierlsBoxOpenEdges_of_mem_boxOpenReachableFrontierDualEdges
    (m := m) (M := M) (ω := ω) hmM (hsubset hed) hebox

/-- If every shifted-dual edge traversed by a circuit is open in the induced dual configuration,
then the circuit is open. -/
theorem isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration
    {ω : EdgeConfiguration 2} {c : DualCircuit}
    (h : (walkEdgeFinset c.walk : Set DualSquareEdge) ⊆ dualSquareConfiguration ω) :
    c.IsOpen ω := by
  intro e he
  let ed : DualSquareEdge := ⟨e, c.walk.edges_subset_edgeSet he⟩
  have hed : ed ∈ walkEdgeFinset c.walk := (mem_walkEdgeFinset_iff c.walk ed).mpr he
  exact h hed

end DualCircuit

/-- A circuit extracted inside the finite frontier graph automatically avoids Grimmett's box-open
support `G_m`, provided the ambient frontier box contains `B(m)`. -/
theorem dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_avoidsBoxEdges
    {m M : ℕ} {ω : EdgeConfiguration 2} {u : DualSquareVertex} (hmM : m ≤ M)
    (w : (boxOpenReachableFrontierDualGraph m M ω).Walk u u) (hw : w.IsCircuit) :
    (dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw).AvoidsBoxEdges m :=
  DualCircuit.avoidsBoxEdges_of_walkEdgeFinset_subset_boxOpenReachableFrontierDualEdges
    hmM (walkEdgeFinset_dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_subset w hw)

/-- Mathlib's edge-connectivity cycle criterion specialized to the finite shifted-dual frontier
graph. If adjacent frontier vertices remain connected after deleting any one edge, they lie on a
cycle in the frontier graph. -/
theorem exists_isCycle_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two
    {m M : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (huv : (boxOpenReachableFrontierDualGraph m M ω).Adj u v)
    (h2 : (boxOpenReachableFrontierDualGraph m M ω).IsEdgeReachable 2 u v) :
    ∃ w : (boxOpenReachableFrontierDualGraph m M ω).Walk u u, w.IsCycle :=
  SimpleGraph.exists_isCycle_of_two_le_isEdgeReachable huv.ne le_rfl h2

/-- Edge-retaining form of the frontier edge-connectivity cycle criterion. If adjacent frontier
vertices remain connected after deleting any one edge, then the chosen frontier edge itself lies
on a simple cycle in the finite frontier graph. -/
theorem exists_isCycle_mem_edge_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two
    {m M : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (huv : (boxOpenReachableFrontierDualGraph m M ω).Adj u v)
    (h2 : (boxOpenReachableFrontierDualGraph m M ω).IsEdgeReachable 2 u v) :
    ∃ x : DualSquareVertex,
      ∃ w : (boxOpenReachableFrontierDualGraph m M ω).Walk x x,
        w.IsCycle ∧ s(u, v) ∈ w.edges := by
  let G := boxOpenReachableFrontierDualGraph m M ω
  have hreach : (G.deleteEdges {s(u, v)}).Reachable u v :=
    (SimpleGraph.isEdgeReachable_two.mp h2) s(u, v)
  simpa [G] using
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := G) (v := u) (w := v)).mp ⟨huv, hreach⟩

/-- Oriented form of the frontier edge-connectivity cycle criterion. The produced simple cycle
starts at the first endpoint and its first step is the chosen adjacent vertex. -/
theorem exists_isCycle_startsWith_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two
    {m M : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (huv : (boxOpenReachableFrontierDualGraph m M ω).Adj u v)
    (h2 : (boxOpenReachableFrontierDualGraph m M ω).IsEdgeReachable 2 u v) :
    ∃ w : (boxOpenReachableFrontierDualGraph m M ω).Walk u u,
      w.IsCycle ∧ w.snd = v := by
  let G := boxOpenReachableFrontierDualGraph m M ω
  have hreach : (G.deleteEdges {s(v, u)}).Reachable v u := by
    simpa [Sym2.eq_swap] using (SimpleGraph.isEdgeReachable_two.mp h2.symm) s(u, v)
  rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk] at hreach
  rcases hreach with ⟨p, hpavoid⟩
  let w : G.Walk u u := SimpleGraph.Walk.cons (show G.Adj u v from huv) p.toPath
  refine ⟨w, ?_, ?_⟩
  · apply SimpleGraph.Path.cons_isCycle
    rw [Sym2.eq_swap]
    intro hmem
    exact hpavoid (p.edges_toPath_subset hmem)
  · simp [w]

/-- If the positive-axis frontier edge is 2-edge-reachable in the finite frontier graph, then it
lies on a shifted-dual simple cycle supported by the frontier. This keeps Grimmett's positive-axis
mark attached to the cycle for the later rotation into `PositiveXAxisMarkedDualCycle`. -/
theorem exists_dualSquare_isCycle_through_positiveXAxisCrossing_of_isEdgeReachable_two
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hadj : (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k))
    (h2 : (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k)) :
    ∃ x : DualSquareVertex, ∃ w : dualSquareGraph.Walk x x,
      w.IsCycle ∧ dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset w ∧
        (walkEdgeFinset w : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases exists_isCycle_mem_edge_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two
      hadj h2 with ⟨x, w, hwcycle, hmem⟩
  let w' : dualSquareGraph.Walk x x := boxOpenReachableFrontierDualGraphWalk w
  have hw'cycle : w'.IsCycle := by
    exact hwcycle.mapLe (boxOpenReachableFrontierDualGraph_le_dualSquareGraph m (m + n) ω)
  have hmarked : dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset w' := by
    rw [mem_walkEdgeFinset_iff]
    change (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex) ∈ w'.edges
    simpa [w', boxOpenReachableFrontierDualGraphWalk, dualPositiveXAxisCrossingEdge_coe,
      SimpleGraph.Walk.edges_mapLe_eq_edges] using hmem
  refine ⟨x, w', hw'cycle, hmarked, ?_⟩
  exact walkEdgeFinset_boxOpenReachableFrontierDualGraphWalk_subset w

/-- Oriented positive-axis version of the frontier cycle bridge. If the positive-axis frontier edge
is 2-edge-reachable, the resulting shifted-dual simple cycle is already rotated so that it starts
with Grimmett's positive-axis crossing. -/
theorem exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hadj : (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k))
    (h2 : (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k)) :
    ∃ w : dualSquareGraph.Walk
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k),
      w.IsCycle ∧ w.snd = dualPositiveXAxisUpperVertex k ∧
        (walkEdgeFinset w : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases
    exists_isCycle_startsWith_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two
      hadj h2 with ⟨w, hwcycle, hfirst⟩
  let w' : dualSquareGraph.Walk
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k) :=
    boxOpenReachableFrontierDualGraphWalk w
  have hw'cycle : w'.IsCycle := by
    exact hwcycle.mapLe (boxOpenReachableFrontierDualGraph_le_dualSquareGraph m (m + n) ω)
  have hstart : w'.snd = dualPositiveXAxisUpperVertex k := by
    exact (boxOpenReachableFrontierDualGraphWalk_snd w).trans hfirst
  refine ⟨w', hw'cycle, hstart, ?_⟩
  exact walkEdgeFinset_boxOpenReachableFrontierDualGraphWalk_subset w

/-- A failed finite frontier always contains a normalized simple shifted-dual cycle through some
positive-axis crossing. This discharges the earlier edge-connectivity placeholder using the
finite-support even-degree theorem for the frontier graph. -/
theorem exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_frontier
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    ∃ k : ℕ, ∃ w : dualSquareGraph.Walk
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k),
      w.IsCycle ∧ w.snd = dualPositiveXAxisUpperVertex k ∧
        (walkEdgeFinset w : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases exists_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph
      m n ω with ⟨k, _hk, hadj⟩
  have h2 :
      (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k) :=
    boxOpenReachableFrontierDualGraph_isEdgeReachable_two_of_adj hadj
  rcases exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two
      hadj h2 with ⟨w, hwcycle, hfirst, hsubset⟩
  exact ⟨k, w, hwcycle, hfirst, hsubset⟩

/-- Open-circuit form of
`exists_dualSquare_isCycle_through_positiveXAxisCrossing_of_isEdgeReachable_two`. Under failed
finite box exit, a 2-edge-reachable positive-axis frontier edge lies on a dual-open simple circuit
that avoids Grimmett's box-open support and remains supported by the finite frontier. -/
theorem exists_open_dualCircuit_through_positiveXAxisCrossing_of_isEdgeReachable_two
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (hadj : (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k))
    (h2 : (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k)) :
    ∃ c : DualCircuit,
      c.walk.IsCycle ∧ c.IsOpen ω ∧ c.AvoidsBoxEdges m ∧
        dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset c.walk ∧
          (walkEdgeFinset c.walk : Set DualSquareEdge) ⊆
            boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases exists_dualSquare_isCycle_through_positiveXAxisCrossing_of_isEdgeReachable_two
      hadj h2 with ⟨x, w, hwcycle, hmarked, hsubset⟩
  let c : DualCircuit :=
    { vertex := x
      walk := w
      isCircuit := hwcycle.isCircuit }
  refine ⟨c, hwcycle, ?_, ?_, hmarked, hsubset⟩
  · have hfrontier :
        (boxOpenReachableFrontierDualEdges m (m + n) ω : Set DualSquareEdge) ⊆
          dualSquareConfiguration ω :=
      boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
        hno
    exact DualCircuit.isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration
      (fun _ he ↦ hfrontier (hsubset he))
  · exact DualCircuit.avoidsBoxEdges_of_walkEdgeFinset_subset_boxOpenReachableFrontierDualEdges
      (Nat.le_add_right m n) hsubset

/-- Oriented open-circuit form of the positive-axis edge-connectivity bridge. The resulting
dual-open simple circuit is already rotated so that its first edge is Grimmett's positive-axis
crossing. -/
theorem exists_open_dualCircuit_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (hadj : (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k))
    (h2 : (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k)) :
    ∃ c : DualCircuit,
      c.vertex = dualPositiveXAxisLowerVertex k ∧ c.walk.IsCycle ∧
        c.walk.snd = dualPositiveXAxisUpperVertex k ∧ c.IsOpen ω ∧ c.AvoidsBoxEdges m ∧
          (walkEdgeFinset c.walk : Set DualSquareEdge) ⊆
            boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two
      hadj h2 with ⟨w, hwcycle, hfirst, hsubset⟩
  let c : DualCircuit :=
    { vertex := dualPositiveXAxisLowerVertex k
      walk := w
      isCircuit := hwcycle.isCircuit }
  refine ⟨c, rfl, hwcycle, hfirst, ?_, ?_, hsubset⟩
  · have hfrontier :
        (boxOpenReachableFrontierDualEdges m (m + n) ω : Set DualSquareEdge) ⊆
          dualSquareConfiguration ω :=
      boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
        hno
    exact DualCircuit.isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration
      (fun _ he ↦ hfrontier (hsubset he))
  · exact DualCircuit.avoidsBoxEdges_of_walkEdgeFinset_subset_boxOpenReachableFrontierDualEdges
      (Nat.le_add_right m n) hsubset

/-- Under failure of finite box exit, the finite shifted-dual frontier contains a dual-open simple
circuit, normalized to start with a positive-axis crossing, and supported by the frontier. The only
remaining planar-selection input for Grimmett's surrounding-circuit step is to show that one such
cycle has odd positive-ray crossing parity (or equivalently makes the left excursion). -/
theorem exists_open_dualCircuit_startsWith_positiveXAxisCrossing_of_not_boxReachesOutside
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n) :
    ∃ k : ℕ, ∃ c : DualCircuit,
      c.vertex = dualPositiveXAxisLowerVertex k ∧ c.walk.IsCycle ∧
        c.walk.snd = dualPositiveXAxisUpperVertex k ∧ c.IsOpen ω ∧ c.AvoidsBoxEdges m ∧
          (walkEdgeFinset c.walk : Set DualSquareEdge) ⊆
            boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases exists_dualPositiveXAxisCrossingEdge_adj_boxOpenReachableFrontierDualGraph
      m n ω with ⟨k, _hk, hadj⟩
  have h2 :
      (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k) :=
    boxOpenReachableFrontierDualGraph_isEdgeReachable_two_of_adj hadj
  rcases exists_open_dualCircuit_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two
      hno hadj h2 with ⟨c, hcvertex, hcycle, hfirst, hopen, havoid, hsubset⟩
  exact ⟨k, c, hcvertex, hcycle, hfirst, hopen, havoid, hsubset⟩

/-- If a frontier-graph edge lies in a 2-edge-reachable block, then under failure of the finite
box-exit event it yields an open shifted-dual circuit supported by the frontier and avoiding
Grimmett's box-open support. The remaining planar task is to prove this edge-connectivity input
for a surrounding frontier edge. -/
theorem exists_open_dualCircuit_of_boxOpenReachableFrontierDualGraph_adj_isEdgeReachable_two
    {m n : ℕ} {ω : EdgeConfiguration 2} {u v : DualSquareVertex}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (huv : (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj u v)
    (h2 : (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2 u v) :
    ∃ c : DualCircuit,
      c.IsOpen ω ∧ c.AvoidsBoxEdges m ∧
        (walkEdgeFinset c.walk : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases exists_isCycle_boxOpenReachableFrontierDualGraph_of_adj_isEdgeReachable_two
      huv h2 with ⟨w, hw⟩
  let c : DualCircuit :=
    dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit w hw.isCircuit
  refine ⟨c, ?_, ?_, ?_⟩
  · exact
      dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_isOpen_of_not_boxReachesOutside
        hno w hw.isCircuit
  · exact
      dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_avoidsBoxEdges
        (m := m) (M := m + n) (ω := ω) (Nat.le_add_right m n) w hw.isCircuit
  · exact walkEdgeFinset_dualCircuitOfBoxOpenReachableFrontierDualGraphCircuit_subset
      w hw.isCircuit

/-- Grimmett's `G_m ∩ F_mᶜ` probability step for the source-faithful box event `G_m`, where
`G_m` is the event that all bonds of `B(m)` are open. -/
theorem exists_bernoulliBondMeasure_real_peierlsBoxOpenEdges_inter_compl_encodedOpenDualCircuitTail_pos_of_mul_lt_one
    {β : ℕ → Type*} [∀ n, Fintype (β n)] (p : I)
    (circuits : ∀ n, β n → DualCircuit)
    (hlen : ∀ n (b : β n), (circuits n b).length = n)
    (encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1))
    (hind : ∀ N : ℕ,
      IndepSet (openEdgeSetEvent 2 (peierlsBoxOpenEdges N))
        (encodedOpenDualCircuitTail circuits N) (bernoulliBondMeasure 2 p))
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    ∃ N : ℕ, 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (encodedOpenDualCircuitTail circuits N)ᶜ) := by
  rcases exists_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one
    p circuits hlen encode h with ⟨N, hNlt⟩
  refine ⟨N, ?_⟩
  have hp : 0 < (p : ℝ) :=
    unitInterval_pos_of_one_sub_mul_cubicConnectiveConstant_lt_one (by norm_num) p h
  have hGpos : 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (peierlsBoxOpenEdges N)) :=
    bernoulliBondMeasure_real_peierlsBoxOpenEdges_pos p N hp
  exact bernoulliBondMeasure_real_inter_compl_pos_of_indepSet p
    (measurableSet_encodedOpenDualCircuitTail circuits N)
    (measurableSet_openEdgeSetEvent 2 (peierlsBoxOpenEdges N))
    (hind N) hGpos hNlt

/-- Source-shaped remaining geometric data for Grimmett's planar Peierls upper bound. This
package no longer assumes the final inequality `p_c(2) ≤ 1 - 1/λ(2)`; instead it records the
length-indexed closed dual circuits, Grimmett's marked-edge/self-avoiding-walk encoding, the
finite open events `G_m`, their independence from the tail `F_m`, and the geometric implication
`G_m ∩ F_mᶜ ⊆ {0 ↔ ∞}`. -/
structure PlanarPeierlsGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- The finite open-edge events `G_m`, represented by their finite edge supports. -/
  openEdges : ℕ → Finset (CubicEdge 2)
  /-- `G_m` is independent of the encoded closed-dual-circuit tail `F_m`. -/
  independent : ∀ (p : I) (N : ℕ),
    IndepSet (openEdgeSetEvent 2 (openEdges N)) (encodedOpenDualCircuitTail circuits N)
      (bernoulliBondMeasure 2 p)
  /-- The geometric implication in Grimmett's proof: if `G_m` occurs and no relevant closed
  dual-circuit tail occurs, then the origin is in an infinite open cluster. -/
  infinite_subset : ∀ N,
    openEdgeSetEvent 2 (openEdges N) ∩ (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsGeometry

/-- The source-shaped Peierls geometry gives positive percolation probability whenever
`(1-p) * λ(2) < 1`. This is the formal version of the end of Grimmett's Peierls argument before
taking the critical supremum. -/
theorem theta_pos_of_one_sub_mul_lt_one (G : PlanarPeierlsGeometry) (p : I)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    0 < theta 2 p := by
  letI : ∀ n, Fintype (G.β n) := G.finite
  rcases exists_bernoulliBondMeasure_real_encodedOpenDualCircuitTail_lt_one
    p G.circuits G.length_eq G.encode h with ⟨N, hNlt⟩
  have hGpos : 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (G.openEdges N)) :=
    bernoulliBondMeasure_real_openEdgeSetEvent_pos 2 p (G.openEdges N)
      (unitInterval_pos_of_one_sub_mul_cubicConnectiveConstant_lt_one (by norm_num) p h)
  have hinter : 0 < (bernoulliBondMeasure 2 p).real
      (openEdgeSetEvent 2 (G.openEdges N) ∩ (encodedOpenDualCircuitTail G.circuits N)ᶜ) :=
    bernoulliBondMeasure_real_inter_compl_pos_of_indepSet p
      (measurableSet_encodedOpenDualCircuitTail G.circuits N)
      (measurableSet_openEdgeSetEvent 2 (G.openEdges N)) (G.independent p N) hGpos hNlt
  unfold theta
  exact hinter.trans_le <| measureReal_mono (G.infinite_subset N) (by
    change setBer((Set.univ : Set (CubicEdge 2)), p)
        {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω} ≠ ∞
    refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top)

/-- The source-shaped Peierls geometry proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 := by
  letI : ∀ n, Fintype (G.β n) := G.finite
  let A : Set ℝ := ((fun p : I ↦ (p : ℝ)) '' {p : I | theta 2 p = 0})
  have hA_nonempty : A.Nonempty := by
    let p0 : I := ⟨0, by norm_num, by norm_num⟩
    refine ⟨0, ?_⟩
    refine ⟨p0, ?_, rfl⟩
    exact theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one 2 p0 (by simp [p0])
  rw [cubicCriticalProbability]
  change sSup A ≤ 1 - 1 / cubicConnectiveConstant 2
  refine csSup_le hA_nonempty ?_
  rintro x ⟨p, hpzero, rfl⟩
  by_contra hnot
  have hp_gt : 1 - 1 / cubicConnectiveConstant 2 < (p : ℝ) := lt_of_not_ge hnot
  have hlambda_pos : 0 < cubicConnectiveConstant 2 := cubicConnectiveConstant_pos (by norm_num)
  have hq_lt_inv : 1 - (p : ℝ) < 1 / cubicConnectiveConstant 2 := by linarith
  have hmul : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1 := by
    rwa [lt_div_iff₀ hlambda_pos] at hq_lt_inv
  have htheta_pos : 0 < theta 2 p := G.theta_pos_of_one_sub_mul_lt_one p hmul
  have hpzero' : theta 2 p = 0 := by simpa using hpzero
  rw [hpzero'] at htheta_pos
  exact (lt_irrefl (0 : ℝ)) htheta_pos

/-- The source-shaped Peierls geometry supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsGeometry) : GrimmettTheorem110Inputs where
  planar_peierls_upper_bound := G.cubicCriticalProbability_le_one_sub_inv

end PlanarPeierlsGeometry

/-- Box-indexed source-shaped Peierls geometry. This matches Grimmett's `F_N` notation more
closely than `PlanarPeierlsGeometry`: the family of relevant closed dual circuits may depend on
the box scale `N`, while the length count for each fixed `N` is still bounded by
`n * σ(n - 1)`. -/
structure PlanarPeierlsBoxIndexedGeometry where
  /-- The finite family of relevant shifted-dual circuits for box scale `N` and length `n`. -/
  β : ℕ → ℕ → Type
  /-- Each box/length family is finite. -/
  finite : ∀ N n, Fintype (β N n)
  /-- The relevant shifted-dual circuits, indexed by box scale and length. -/
  circuits : ∀ N n, β N n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ N n (b : β N n), (circuits N n b).length = n
  /-- Grimmett's injection `ρ_N(n) ≤ n * σ(n - 1)` for each box scale `N`. -/
  encode : ∀ N n, β N n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- Grimmett's `G_N` is independent of the box-indexed closed-dual-circuit tail `F_N`. -/
  independent : ∀ (p : I) (N : ℕ),
    IndepSet (openEdgeSetEvent 2 (peierlsBoxOpenEdges N))
      (boxIndexedOpenDualCircuitTail circuits N) (bernoulliBondMeasure 2 p)
  /-- The geometric implication in Grimmett's proof for indexed tails: if `G_N` occurs and no
  relevant `F_N` closed-dual-circuit occurs, then the origin is in an infinite open cluster. -/
  infinite_subset : ∀ N,
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (boxIndexedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsBoxIndexedGeometry

/-- Box-indexed Peierls geometry gives positive percolation probability whenever
`(1-p) * λ(2) < 1`. -/
theorem theta_pos_of_one_sub_mul_lt_one (G : PlanarPeierlsBoxIndexedGeometry) (p : I)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    0 < theta 2 p := by
  letI : ∀ N n, Fintype (G.β N n) := G.finite
  rcases
    exists_bernoulliBondMeasure_real_peierlsBoxOpenEdges_inter_compl_boxIndexedOpenDualCircuitTail_pos_of_mul_lt_one
      p G.circuits G.length_eq G.encode (fun N ↦ G.independent p N) h with
    ⟨N, hinter⟩
  unfold theta
  exact hinter.trans_le <| measureReal_mono (G.infinite_subset N) (by
    change setBer((Set.univ : Set (CubicEdge 2)), p)
        {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω} ≠ ∞
    refine ne_of_lt ((measure_mono (Set.subset_univ _)).trans_lt ?_)
    rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact ENNReal.one_lt_top)

/-- Box-indexed Peierls geometry proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsBoxIndexedGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 := by
  let A : Set ℝ := ((fun p : I ↦ (p : ℝ)) '' {p : I | theta 2 p = 0})
  have hA_nonempty : A.Nonempty := by
    let p0 : I := ⟨0, by norm_num, by norm_num⟩
    refine ⟨0, ?_⟩
    refine ⟨p0, ?_, rfl⟩
    exact theta_eq_zero_of_mul_cubicConnectiveConstant_lt_one 2 p0 (by simp [p0])
  rw [cubicCriticalProbability]
  change sSup A ≤ 1 - 1 / cubicConnectiveConstant 2
  refine csSup_le hA_nonempty ?_
  rintro x ⟨p, hpzero, rfl⟩
  by_contra hnot
  have hp_gt : 1 - 1 / cubicConnectiveConstant 2 < (p : ℝ) := lt_of_not_ge hnot
  have hlambda_pos : 0 < cubicConnectiveConstant 2 := cubicConnectiveConstant_pos (by norm_num)
  have hq_lt_inv : 1 - (p : ℝ) < 1 / cubicConnectiveConstant 2 := by linarith
  have hmul : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1 := by
    rwa [lt_div_iff₀ hlambda_pos] at hq_lt_inv
  have htheta_pos : 0 < theta 2 p := G.theta_pos_of_one_sub_mul_lt_one p hmul
  have hpzero' : theta 2 p = 0 := by simpa using hpzero
  rw [hpzero'] at htheta_pos
  exact (lt_irrefl (0 : ℝ)) htheta_pos

/-- Box-indexed Peierls geometry supplies the final input package used by the public Theorem
1.10 reductions. -/
theorem toGrimmettTheorem110Inputs
    (G : PlanarPeierlsBoxIndexedGeometry) : GrimmettTheorem110Inputs where
  planar_peierls_upper_bound := G.cubicCriticalProbability_le_one_sub_inv

end PlanarPeierlsBoxIndexedGeometry

/-- A finite-window version of the remaining source-shaped Peierls geometry. This package asks
for independence only from every finite encoded window `F_{m,M}`; the countable tail independence
required by `PlanarPeierlsGeometry` follows by monotone convergence. -/
structure PlanarPeierlsWindowGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- The finite open-edge events `G_m`, represented by their finite edge supports. -/
  openEdges : ℕ → Finset (CubicEdge 2)
  /-- `G_m` is independent of each finite encoded closed-dual-circuit window. -/
  independent_window : ∀ (p : I) (N M : ℕ),
    IndepSet (openEdgeSetEvent 2 (openEdges N)) (encodedOpenDualCircuitWindow circuits N M)
      (bernoulliBondMeasure 2 p)
  /-- The geometric implication in Grimmett's proof: if `G_m` occurs and no relevant closed
  dual-circuit tail occurs, then the origin is in an infinite open cluster. -/
  infinite_subset : ∀ N,
    openEdgeSetEvent 2 (openEdges N) ∩ (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsWindowGeometry

/-- Finite-window Peierls geometry supplies the tail-level Peierls geometry by continuity of
measure along the increasing finite windows. -/
def toPlanarPeierlsGeometry (G : PlanarPeierlsWindowGeometry) : PlanarPeierlsGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  openEdges := G.openEdges
  independent := by
    intro p N
    letI : ∀ n, Fintype (G.β n) := G.finite
    exact indepSet_openEdgeSetEvent_encodedOpenDualCircuitTail_of_windows p
      (G.openEdges N) G.circuits N (G.independent_window p N)
  infinite_subset := G.infinite_subset

/-- The finite-window Peierls package gives positive percolation probability whenever
`(1-p) * λ(2) < 1`. -/
theorem theta_pos_of_one_sub_mul_lt_one (G : PlanarPeierlsWindowGeometry) (p : I)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    0 < theta 2 p :=
  G.toPlanarPeierlsGeometry.theta_pos_of_one_sub_mul_lt_one p h

/-- The finite-window Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsWindowGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The finite-window Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsWindowGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsWindowGeometry

/-- A support-level version of the remaining source-shaped Peierls geometry. This package replaces
the finite-window independence assumption by the geometric disjointness of finite primal supports:
`G_m` uses `openEdges m`, while the finite dual-circuit window uses the crossed primal bonds of
the circuits in that window. -/
structure PlanarPeierlsSupportGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- The finite open-edge events `G_m`, represented by their finite edge supports. -/
  openEdges : ℕ → Finset (CubicEdge 2)
  /-- The finite support disjointness that implies `G_m` is independent of each finite
  closed-dual-circuit window. -/
  support_disjoint : ∀ N M,
    letI : ∀ n, Fintype (β n) := finite
    Disjoint ((openEdges N : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      ((encodedOpenDualCircuitWindowPrimalSupport circuits N M : Finset (CubicEdge 2)) :
        Set (CubicEdge 2))
  /-- The geometric implication in Grimmett's proof: if `G_m` occurs and no relevant closed
  dual-circuit tail occurs, then the origin is in an infinite open cluster. -/
  infinite_subset : ∀ N,
    openEdgeSetEvent 2 (openEdges N) ∩ (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsSupportGeometry

/-- Support-level Peierls geometry supplies the finite-window Peierls package by finite product
measure independence on disjoint coordinate supports. -/
def toPlanarPeierlsWindowGeometry (G : PlanarPeierlsSupportGeometry) :
    PlanarPeierlsWindowGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  openEdges := G.openEdges
  independent_window := by
    intro p N M
    letI : ∀ n, Fintype (G.β n) := G.finite
    exact indepSet_openEdgeSetEvent_encodedOpenDualCircuitWindow_of_disjoint_support p
      (G.openEdges N) G.circuits N M (G.support_disjoint N M)
  infinite_subset := G.infinite_subset

/-- Support-level Peierls geometry supplies the tail-level Peierls geometry. -/
def toPlanarPeierlsGeometry (G : PlanarPeierlsSupportGeometry) : PlanarPeierlsGeometry :=
  G.toPlanarPeierlsWindowGeometry.toPlanarPeierlsGeometry

/-- The support-level Peierls package gives positive percolation probability whenever
`(1-p) * λ(2) < 1`. -/
theorem theta_pos_of_one_sub_mul_lt_one (G : PlanarPeierlsSupportGeometry) (p : I)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    0 < theta 2 p :=
  G.toPlanarPeierlsGeometry.theta_pos_of_one_sub_mul_lt_one p h

/-- The support-level Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsSupportGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The support-level Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsSupportGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsSupportGeometry

/-- A box-event version of the remaining source-shaped Peierls geometry, matching Grimmett's
elementary proof after (1.18). Here `G_m` is the event that all bonds of the box `B(m)` are open.
The remaining geometric inputs are the closed dual circuits surrounding `B(m)`, their
marked-edge/self-avoiding-walk encoding, support disjointness from the box bonds, and the
separation implication `G_m ∩ F_mᶜ ⊆ {0 ↔ ∞}`. -/
structure PlanarPeierlsBoxGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- The box-open event `G_N` is disjoint from the primal bonds crossed by each finite
  closed-dual-circuit window `F_{N,M}`. -/
  support_disjoint : ∀ N M,
    letI : ∀ n, Fintype (β n) := finite
    Disjoint ((peierlsBoxOpenEdges N : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      ((encodedOpenDualCircuitWindowPrimalSupport circuits N M : Finset (CubicEdge 2)) :
        Set (CubicEdge 2))
  /-- The geometric implication in Grimmett's proof for the box event `G_N`: if every bond of
  `B(N)` is open and no relevant closed dual circuit surrounds the box, then the origin is in an
  infinite open cluster. -/
  infinite_subset : ∀ N,
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsBoxGeometry

/-- The box-event Peierls package is a support-level Peierls package with
`openEdges N = peierlsBoxOpenEdges N`. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsBoxGeometry) :
    PlanarPeierlsSupportGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  openEdges := peierlsBoxOpenEdges
  support_disjoint := by
    intro N M
    letI : ∀ n, Fintype (G.β n) := G.finite
    exact G.support_disjoint N M
  infinite_subset := G.infinite_subset

/-- The box-event Peierls package supplies the finite-window Peierls package. -/
noncomputable def toPlanarPeierlsWindowGeometry (G : PlanarPeierlsBoxGeometry) :
    PlanarPeierlsWindowGeometry :=
  G.toPlanarPeierlsSupportGeometry.toPlanarPeierlsWindowGeometry

/-- The box-event Peierls package supplies the tail-level Peierls package. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsBoxGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsSupportGeometry.toPlanarPeierlsGeometry

/-- The box-event Peierls package gives positive percolation probability whenever
`(1-p) * λ(2) < 1`. -/
theorem theta_pos_of_one_sub_mul_lt_one (G : PlanarPeierlsBoxGeometry) (p : I)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    0 < theta 2 p :=
  G.toPlanarPeierlsGeometry.theta_pos_of_one_sub_mul_lt_one p h

/-- The box-event Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsBoxGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The box-event Peierls package supplies the final input package used by the public Theorem
1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsBoxGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsBoxGeometry

/-- A per-circuit support version of the source-shaped box Peierls geometry. Instead of asking for
finite-window disjointness at once, this package asks for the geometric fact circuit-by-circuit:
every relevant circuit of length at least `N` avoids the bonds of `B(N)`. -/
structure PlanarPeierlsBoxCircuitGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- Each relevant circuit in the tail avoids the box bonds. This is the per-circuit geometric
  version of the finite-window support disjointness needed for independence. -/
  circuit_avoids_box : ∀ N n, N ≤ n → ∀ b : β n, (circuits n b).AvoidsBoxEdges N
  /-- The geometric implication in Grimmett's proof for the box event `G_N`: if every bond of
  `B(N)` is open and no relevant closed dual circuit surrounds the box, then the origin is in an
  infinite open cluster. -/
  infinite_subset : ∀ N,
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsBoxCircuitGeometry

/-- Per-circuit box Peierls geometry supplies the box-event Peierls package by taking the union of
the crossed primal supports over the finite window. -/
noncomputable def toPlanarPeierlsBoxGeometry (G : PlanarPeierlsBoxCircuitGeometry) :
    PlanarPeierlsBoxGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  support_disjoint := by
    intro N M
    letI : ∀ n, Fintype (G.β n) := G.finite
    exact disjoint_encodedOpenDualCircuitWindowPrimalSupport_of_forall
      (peierlsBoxOpenEdges N) G.circuits N M (by
        intro k b
        exact G.circuit_avoids_box N (N + (k : ℕ)) (by omega) b)
  infinite_subset := G.infinite_subset

/-- Per-circuit box Peierls geometry supplies support-level Peierls geometry. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsBoxCircuitGeometry) :
    PlanarPeierlsSupportGeometry :=
  G.toPlanarPeierlsBoxGeometry.toPlanarPeierlsSupportGeometry

/-- Per-circuit box Peierls geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsBoxCircuitGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxGeometry.toPlanarPeierlsGeometry

/-- The per-circuit box Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsBoxCircuitGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The per-circuit box Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsBoxCircuitGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsBoxCircuitGeometry

/-- A straight-path version of the remaining source-shaped Peierls geometry. This fixes Grimmett's
finite open event `G_N` to the straight coordinate path from the origin, so the remaining fields are
only the closed dual circuits, their marked-edge/self-avoiding-walk encoding, support disjointness
from that straight path, and the separation implication. -/
structure PlanarPeierlsStraightGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- The straight finite open path `G_N` is disjoint from the primal bonds crossed by each finite
  closed-dual-circuit window. -/
  support_disjoint : ∀ N M,
    letI : ∀ n, Fintype (β n) := finite
    Disjoint ((peierlsStraightOpenPathEdges N : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      ((encodedOpenDualCircuitWindowPrimalSupport circuits N M : Finset (CubicEdge 2)) :
        Set (CubicEdge 2))
  /-- The geometric implication in Grimmett's proof for the concrete straight `G_N`: if the straight
  path is open and no relevant closed dual-circuit tail occurs, then the origin is in an infinite
  open cluster. -/
  infinite_subset : ∀ N,
    openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N) ∩
        (encodedOpenDualCircuitTail circuits N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsStraightGeometry

/-- The straight-path Peierls package is a support-level Peierls package with
`openEdges N = peierlsStraightOpenPathEdges N`. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsStraightGeometry) :
    PlanarPeierlsSupportGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  openEdges := peierlsStraightOpenPathEdges
  support_disjoint := by
    intro N M
    letI : ∀ n, Fintype (G.β n) := G.finite
    exact G.support_disjoint N M
  infinite_subset := G.infinite_subset

/-- The straight-path Peierls package supplies the finite-window Peierls package. -/
noncomputable def toPlanarPeierlsWindowGeometry (G : PlanarPeierlsStraightGeometry) :
    PlanarPeierlsWindowGeometry :=
  G.toPlanarPeierlsSupportGeometry.toPlanarPeierlsWindowGeometry

/-- The straight-path Peierls package supplies the tail-level Peierls package. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsStraightGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsSupportGeometry.toPlanarPeierlsGeometry

/-- The straight-path Peierls package gives positive percolation probability whenever
`(1-p) * λ(2) < 1`. -/
theorem theta_pos_of_one_sub_mul_lt_one (G : PlanarPeierlsStraightGeometry) (p : I)
    (h : (1 - (p : ℝ)) * cubicConnectiveConstant 2 < 1) :
    0 < theta 2 p :=
  G.toPlanarPeierlsGeometry.theta_pos_of_one_sub_mul_lt_one p h

/-- The straight-path Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsStraightGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The straight-path Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsStraightGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsStraightGeometry

/-- Data recording how the tail of a shifted-dual closed walk is represented by a counted
self-avoiding direction word from the tail's actual starting vertex. The equality field is the
reconstruction hook needed for the later injectivity part of Grimmett's circuit coding. -/
structure DualCycleTailCodeData {u : DualSquareVertex} (w : dualSquareGraph.Walk u u) where
  saw : SelfAvoidingWalk 2 (w.length - 1)
  endpoint_eq : cubicEndpointFrom w.snd saw.1.toList = u
  tail_eq : (cubicWalkFrom w.snd saw.1.toList).copy rfl endpoint_eq = w.tail

/-- The tail of a shifted-dual simple cycle, after deleting the marked return edge, admits a
canonical self-avoiding direction-word representative of length `n - 1`. -/
theorem nonempty_dualCycleTailCodeData {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) :
    Nonempty (DualCycleTailCodeData w) := by
  rcases exists_cubicWalkFrom_copy_eq w.tail with ⟨steps, hend, hcopy, hlen⟩
  let stepsV : List.Vector (CubicDirection 2) (w.length - 1) := ⟨steps, by
    have htail_len : w.tail.length + 1 = w.length :=
      SimpleGraph.Walk.length_tail_add_one hw.not_nil
    omega⟩
  have htail_path : w.tail.IsPath := hw.isPath_tail
  have hpath_word : (cubicWalkFrom w.snd steps).IsPath := by
    have hcopy_path : ((cubicWalkFrom w.snd steps).copy rfl hend).IsPath := by
      simpa [hcopy] using htail_path
    simpa using hcopy_path
  let saw : SelfAvoidingWalk 2 (w.length - 1) :=
    selfAvoidingWalkOfPathWord (x := w.snd) stepsV (by simpa [stepsV] using hpath_word)
  refine ⟨⟨saw, ?_, ?_⟩⟩
  · simpa [saw, selfAvoidingWalkOfPathWord, stepsV] using hend
  · simpa [saw, selfAvoidingWalkOfPathWord, stepsV] using hcopy

/-- A chosen reconstruction package for the tail of a shifted-dual simple cycle. -/
noncomputable def dualCycleTailCodeData {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) :
    DualCycleTailCodeData w :=
  Classical.choice (nonempty_dualCycleTailCodeData w hw)

/-- The tail of a shifted-dual simple cycle, after deleting the marked return edge, is a
self-avoiding direction word of length `n - 1`. This is the path half of Grimmett's coding
`ρ(n) ≤ n σ(n - 1)`: the initial marked edge supplies the `n`, and the remaining simple path is
counted by `σ(n - 1)`. -/
noncomputable def selfAvoidingWalkOfDualCycleTail {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) :
    SelfAvoidingWalk 2 (w.length - 1) :=
  (dualCycleTailCodeData w hw).saw

/-- The selected self-avoiding direction word for a dual cycle ends at the cycle's base vertex
when started from the first vertex of the tail. -/
theorem selfAvoidingWalkOfDualCycleTail_endpoint_eq {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) :
    cubicEndpointFrom w.snd (selfAvoidingWalkOfDualCycleTail w hw).1.toList = u :=
  (dualCycleTailCodeData w hw).endpoint_eq

/-- The selected self-avoiding direction word reconstructs the tail of the original dual cycle. -/
theorem selfAvoidingWalkOfDualCycleTail_copy_eq {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) :
    (cubicWalkFrom w.snd (selfAvoidingWalkOfDualCycleTail w hw).1.toList).copy rfl
      (selfAvoidingWalkOfDualCycleTail_endpoint_eq w hw) = w.tail :=
  (dualCycleTailCodeData w hw).tail_eq

/-- A shifted-dual simple cycle is reconstructed from its first edge together with the selected
self-avoiding tail word. This is the deterministic decoding hook behind the marked-edge
`ρ(n) ≤ n σ(n - 1)` injection. -/
theorem dualCycle_eq_cons_selfAvoidingWalkOfDualCycleTail {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) :
    SimpleGraph.Walk.cons (w.adj_snd hw.not_nil)
      ((cubicWalkFrom w.snd (selfAvoidingWalkOfDualCycleTail w hw).1.toList).copy rfl
        (selfAvoidingWalkOfDualCycleTail_endpoint_eq w hw)) = w := by
  rw [selfAvoidingWalkOfDualCycleTail_copy_eq, SimpleGraph.Walk.cons_tail_eq w hw.not_nil]

/-- The code used in Grimmett's circuit-counting estimate `ρ(n) ≤ n * σ(n - 1)`: a marked
choice among at most `n` possible crossing positions together with a self-avoiding walk of length
`n - 1`. -/
abbrev PeierlsCircuitCode (n : ℕ) := Fin n × SelfAvoidingWalk 2 (n - 1)

/-- A shifted-dual closed walk is normalized at the positive horizontal ray coordinate `k` when
its first edge is the vertical shifted-dual edge crossing that ray at `k`. This is the concrete
mark used in Grimmett's `ρ(n) ≤ n σ(n - 1)` circuit count. -/
def dualCycleStartsWithPositiveXAxisCrossing {u : DualSquareVertex} (k : ℕ)
    (w : dualSquareGraph.Walk u u) : Prop :=
  u = dualPositiveXAxisLowerVertex k ∧ w.snd = dualPositiveXAxisUpperVertex k

/-- A closed walk normalized at the positive horizontal ray has a unique crossing coordinate. -/
theorem dualCycleStartsWithPositiveXAxisCrossing_unique
    {u : DualSquareVertex} {k l : ℕ} {w : dualSquareGraph.Walk u u}
    (hk : dualCycleStartsWithPositiveXAxisCrossing k w)
    (hl : dualCycleStartsWithPositiveXAxisCrossing l w) :
    k = l :=
  dualPositiveXAxisLowerVertex_injective (hk.1.symm.trans hl.1)

/-- The lower half-plane for shifted-dual vertices, relative to the horizontal primal axis. A
shifted-dual vertical edge crosses the horizontal axis exactly when its endpoints lie on opposite
sides of this predicate. -/
def dualLowerHalfPlane (z : DualSquareVertex) : Prop :=
  z 1 ≤ -1

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V}

/-- An unordered edge crosses the cut defined by a vertex predicate when its two endpoints lie on
opposite sides of the predicate. This is the graph-theoretic parity replacement for a ray-crossing
count. -/
def edgeCrossesSet (P : V → Prop) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y : V ↦ (P x ∧ ¬ P y) ∨ (P y ∧ ¬ P x), by
    intro x y
    apply propext
    tauto⟩

@[simp]
theorem edgeCrossesSet_mk (P : V → Prop) (x y : V) :
    edgeCrossesSet P s(x, y) ↔ ((P x ∧ ¬ P y) ∨ (P y ∧ ¬ P x)) := by
  simp [edgeCrossesSet, Sym2.lift_mk]

/-- Boolean form of `edgeCrossesSet`, used for `List.countP`. -/
def edgeCrossesSetBool (P : V → Prop) [DecidablePred P] : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y : V ↦ decide ((P x ∧ ¬ P y) ∨ (P y ∧ ¬ P x)), by
    intro x y
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    tauto⟩

@[simp]
theorem edgeCrossesSetBool_mk (P : V → Prop) [DecidablePred P] (x y : V) :
    edgeCrossesSetBool P s(x, y) =
      decide ((P x ∧ ¬ P y) ∨ (P y ∧ ¬ P x)) := by
  simp [edgeCrossesSetBool, Sym2.lift_mk]

@[simp]
theorem edgeCrossesSetBool_eq_true (P : V → Prop) [DecidablePred P] (e : Sym2 V) :
    edgeCrossesSetBool P e = true ↔ edgeCrossesSet P e := by
  induction e using Sym2.ind
  simp [edgeCrossesSetBool, edgeCrossesSet, Sym2.lift_mk]

/-- Along any walk, the parity of crossings of a cut is the parity of whether the endpoints lie
on opposite sides of the cut. -/
theorem odd_countP_edges_edgeCrossesSet_iff (P : V → Prop) [DecidablePred P]
    {u v : V} (w : G.Walk u v) :
    Odd (w.edges.countP (edgeCrossesSetBool P)) ↔
      ((P u ∧ ¬ P v) ∨ (P v ∧ ¬ P u)) := by
  induction w with
  | nil => simp
  | @cons u v w h p ih =>
      simp [SimpleGraph.Walk.edges_cons]
      by_cases hu : P u <;> by_cases hv : P v <;> by_cases hw : P w <;>
        simp [edgeCrossesSetBool, Sym2.lift_mk, hu, hv, hw, Nat.not_odd_iff_even] at ih ⊢
      all_goals first | assumption | simpa [Nat.even_add_one] using ih |
        simpa [Nat.odd_add_one] using ih

/-- A closed walk crosses any cut an even number of times, counted with edge multiplicity. -/
theorem even_countP_edges_edgeCrossesSet_of_closed (P : V → Prop) [DecidablePred P]
    {u : V} (w : G.Walk u u) :
    Even (w.edges.countP (edgeCrossesSetBool P)) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  exact (by simpa using (odd_countP_edges_edgeCrossesSet_iff P w).mp hodd)

end Walk
end SimpleGraph

/-- Lower endpoint of the shifted-dual vertical edge crossing the horizontal axis at integer
coordinate `x`. The existing `dualPositiveXAxisLowerVertex` is this definition restricted to
nonnegative integer coordinates. -/
def dualXAxisLowerVertex (x : ℤ) : DualSquareVertex :=
  fun i ↦ if i = 0 then x else -1

/-- Upper endpoint of the shifted-dual vertical edge crossing the horizontal axis at integer
coordinate `x`. -/
def dualXAxisUpperVertex (x : ℤ) : DualSquareVertex :=
  cubicStepFrom (dualXAxisLowerVertex x) (1, true)

@[simp]
theorem dualXAxisLowerVertex_zero (x : ℤ) : dualXAxisLowerVertex x 0 = x := by
  simp [dualXAxisLowerVertex]

@[simp]
theorem dualXAxisLowerVertex_one (x : ℤ) : dualXAxisLowerVertex x 1 = -1 := by
  simp [dualXAxisLowerVertex]

@[simp]
theorem dualXAxisUpperVertex_zero (x : ℤ) : dualXAxisUpperVertex x 0 = x := by
  simp [dualXAxisUpperVertex, dualXAxisLowerVertex, cubicStepFrom, cubicDirectionIncrement]

@[simp]
theorem dualXAxisUpperVertex_one (x : ℤ) : dualXAxisUpperVertex x 1 = 0 := by
  simp [dualXAxisUpperVertex, dualXAxisLowerVertex, cubicStepFrom, cubicDirectionIncrement]

/-- The shifted-dual vertical edge crossing the horizontal axis at integer coordinate `x`. -/
def dualXAxisCrossingEdge (x : ℤ) : DualSquareEdge :=
  ⟨s(dualXAxisLowerVertex x, dualXAxisUpperVertex x), by
    rw [SimpleGraph.mem_edgeSet]
    exact cubicGraph_adj_stepFrom (dualXAxisLowerVertex x) (1, true)⟩

@[simp]
theorem dualXAxisCrossingEdge_coe (x : ℤ) :
    (dualXAxisCrossingEdge x : Sym2 DualSquareVertex) =
      s(dualXAxisLowerVertex x, dualXAxisUpperVertex x) :=
  rfl

theorem dualXAxisLowerVertex_nat (k : ℕ) :
    dualXAxisLowerVertex (k : ℤ) = dualPositiveXAxisLowerVertex k := by
  ext i
  fin_cases i <;> simp [dualXAxisLowerVertex, dualPositiveXAxisLowerVertex]

theorem dualXAxisUpperVertex_nat (k : ℕ) :
    dualXAxisUpperVertex (k : ℤ) = dualPositiveXAxisUpperVertex k := by
  simp [dualXAxisUpperVertex, dualPositiveXAxisUpperVertex, dualXAxisLowerVertex_nat]

theorem dualXAxisCrossingEdge_nat (k : ℕ) :
    dualXAxisCrossingEdge (k : ℤ) = dualPositiveXAxisCrossingEdge k := by
  apply Subtype.ext
  simp [dualXAxisCrossingEdge_coe, dualPositiveXAxisCrossingEdge_coe,
    dualXAxisLowerVertex_nat, dualXAxisUpperVertex_nat]

/-- Any shifted-dual edge crossing the lower/upper half-plane cut is one of the vertical x-axis
crossing edges. This is the coordinate form of the fact that the shifted dual lattice avoids the
ray's endpoints. -/
theorem exists_dualXAxisCrossingEdge_of_edgeCrossesDualLowerHalfPlane {e : DualSquareEdge}
    (hcut :
      SimpleGraph.Walk.edgeCrossesSet dualLowerHalfPlane (e : Sym2 DualSquareVertex)) :
    ∃ x : ℤ, e = dualXAxisCrossingEdge x := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      rw [SimpleGraph.Walk.edgeCrossesSet_mk, dualLowerHalfPlane] at hcut
      rw [SimpleGraph.mem_edgeSet] at he
      rcases (cubicGraph_adj_iff_exists_stepFrom a b).mp he with ⟨dir, rfl⟩
      rcases dir with ⟨i, sign⟩
      fin_cases i
      · exfalso
        simp [cubicStepFrom, cubicDirectionIncrement, dualLowerHalfPlane] at hcut
        omega
      · cases sign
        · have ha1 : a 1 = 0 := by
            simp [cubicStepFrom, cubicDirectionIncrement, dualLowerHalfPlane] at hcut
            omega
          refine ⟨a 0, ?_⟩
          apply Subtype.ext
          have hlower :
              cubicStepFrom a ((1 : Fin 2), false) = dualXAxisLowerVertex (a 0) := by
            ext j
            fin_cases j <;>
              simp [dualXAxisLowerVertex, cubicStepFrom, cubicDirectionIncrement, ha1]
          have hupper : a = dualXAxisUpperVertex (a 0) := by
            ext j
            fin_cases j <;>
              simp [dualXAxisUpperVertex, dualXAxisLowerVertex, cubicStepFrom,
                cubicDirectionIncrement, ha1]
          rw [dualXAxisCrossingEdge_coe]
          change s(a, cubicStepFrom a ((1 : Fin 2), false)) =
            s(dualXAxisLowerVertex (a 0), dualXAxisUpperVertex (a 0))
          have hs1 :
              s(a, cubicStepFrom a ((1 : Fin 2), false)) =
                s(dualXAxisUpperVertex (a 0), cubicStepFrom a ((1 : Fin 2), false)) :=
            congrArg (fun z : DualSquareVertex ↦
              s(z, cubicStepFrom a ((1 : Fin 2), false))) hupper
          have hs2 :
              s(dualXAxisUpperVertex (a 0), cubicStepFrom a ((1 : Fin 2), false)) =
                s(dualXAxisUpperVertex (a 0), dualXAxisLowerVertex (a 0)) :=
            congrArg (fun z : DualSquareVertex ↦ s(dualXAxisUpperVertex (a 0), z)) hlower
          exact hs1.trans (hs2.trans Sym2.eq_swap)
        · have ha1 : a 1 = -1 := by
            simp [cubicStepFrom, cubicDirectionIncrement, dualLowerHalfPlane] at hcut
            omega
          refine ⟨a 0, ?_⟩
          apply Subtype.ext
          have hlower : a = dualXAxisLowerVertex (a 0) := by
            ext j
            fin_cases j <;> simp [dualXAxisLowerVertex, ha1]
          have hupper :
              cubicStepFrom a ((1 : Fin 2), true) = dualXAxisUpperVertex (a 0) := by
            rw [hlower]
            rfl
          rw [dualXAxisCrossingEdge_coe]
          change s(a, cubicStepFrom a ((1 : Fin 2), true)) =
            s(dualXAxisLowerVertex (a 0), dualXAxisUpperVertex (a 0))
          have hs1 :
              s(a, cubicStepFrom a ((1 : Fin 2), true)) =
                s(dualXAxisLowerVertex (a 0), cubicStepFrom a ((1 : Fin 2), true)) :=
            congrArg (fun z : DualSquareVertex ↦
              s(z, cubicStepFrom a ((1 : Fin 2), true))) hlower
          have hs2 :
              s(dualXAxisLowerVertex (a 0), cubicStepFrom a ((1 : Fin 2), true)) =
                s(dualXAxisLowerVertex (a 0), dualXAxisUpperVertex (a 0)) :=
            congrArg (fun z : DualSquareVertex ↦ s(dualXAxisLowerVertex (a 0), z)) hupper
          exact hs1.trans hs2

/-- Positive-ray shifted-dual crossing edges cross the lower/upper half-plane cut. -/
theorem edgeCrossesDualLowerHalfPlane_dualPositiveXAxisCrossingEdge (k : ℕ) :
    SimpleGraph.Walk.edgeCrossesSet dualLowerHalfPlane
      (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex) := by
  simp [dualPositiveXAxisCrossingEdge_coe, SimpleGraph.Walk.edgeCrossesSet_mk,
    dualLowerHalfPlane]

/-- Boolean predicate for positive horizontal ray shifted-dual crossing edges, used for
edge-list counts. It is noncomputable because the coordinate is existentially quantified over
`ℕ`, just like the corresponding finset filters use `classical`. -/
noncomputable def isDualPositiveXAxisCrossingEdge (e : Sym2 DualSquareVertex) : Bool := by
  classical
  exact decide (∃ k : ℕ, e = (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex))

@[simp]
theorem isDualPositiveXAxisCrossingEdge_eq_true (e : Sym2 DualSquareVertex) :
    isDualPositiveXAxisCrossingEdge e = true ↔
      ∃ k : ℕ, e = (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex) := by
  classical
  simp [isDualPositiveXAxisCrossingEdge]

/-- Boolean predicate for positive horizontal ray crossing edges at the fixed-edge subtype level. -/
noncomputable def isDualPositiveXAxisCrossingDualEdge (e : DualSquareEdge) : Bool := by
  classical
  exact decide (∃ k : ℕ, e = dualPositiveXAxisCrossingEdge k)

@[simp]
theorem isDualPositiveXAxisCrossingDualEdge_eq_true (e : DualSquareEdge) :
    isDualPositiveXAxisCrossingDualEdge e = true ↔
      ∃ k : ℕ, e = dualPositiveXAxisCrossingEdge k := by
  classical
  simp [isDualPositiveXAxisCrossingDualEdge]

@[simp]
theorem isDualPositiveXAxisCrossingDualEdge_coe (e : DualSquareEdge) :
    isDualPositiveXAxisCrossingEdge (e : Sym2 DualSquareVertex) =
      isDualPositiveXAxisCrossingDualEdge e := by
  classical
  rw [Bool.eq_iff_iff]
  simp only [isDualPositiveXAxisCrossingEdge_eq_true,
    isDualPositiveXAxisCrossingDualEdge_eq_true]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩

@[simp]
theorem isDualPositiveXAxisCrossingDualEdge_mk (e : Sym2 DualSquareVertex)
    (h : e ∈ dualSquareGraph.edgeSet) :
    isDualPositiveXAxisCrossingDualEdge (⟨e, h⟩ : DualSquareEdge) =
      isDualPositiveXAxisCrossingEdge e :=
  (isDualPositiveXAxisCrossingDualEdge_coe (⟨e, h⟩ : DualSquareEdge)).symm

/-- If a shifted-dual cycle is normalized at the positive horizontal ray coordinate `k`, then the
corresponding positive-axis crossing edge occurs in the cycle. -/
theorem dualPositiveXAxisCrossingEdge_mem_walkEdgeFinset_of_startsWith
    {u : DualSquareVertex} {k : ℕ} {w : dualSquareGraph.Walk u u}
    (hw : w.IsCycle) (hstart : dualCycleStartsWithPositiveXAxisCrossing k w) :
    dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset w := by
  rw [mem_walkEdgeFinset_iff]
  have hfirst : s(u, w.snd) ∈ w.edges := by
    rw [← SimpleGraph.Walk.cons_tail_eq w hw.not_nil]
    simp [SimpleGraph.Walk.edges_cons]
  simpa [dualPositiveXAxisCrossingEdge_coe, hstart.1, hstart.2] using hfirst

/-- The positive horizontal ray crossing edges used by a shifted-dual walk. This is the finite
parity-counting replacement for the topological phrase "the origin lies inside the circuit": a
simple dual cycle surrounds the origin when this finite crossing set has odd cardinality. -/
noncomputable def dualWalkPositiveXAxisCrossingEdges {u v : DualSquareVertex}
    (w : dualSquareGraph.Walk u v) : Finset DualSquareEdge := by
  classical
  exact (walkEdgeFinset w).filter fun e : DualSquareEdge ↦
    ∃ k : ℕ, e = dualPositiveXAxisCrossingEdge k

@[simp]
theorem mem_dualWalkPositiveXAxisCrossingEdges {u v : DualSquareVertex}
    (w : dualSquareGraph.Walk u v) (e : DualSquareEdge) :
    e ∈ dualWalkPositiveXAxisCrossingEdges w ↔
      e ∈ walkEdgeFinset w ∧ ∃ k : ℕ, e = dualPositiveXAxisCrossingEdge k := by
  classical
  simp [dualWalkPositiveXAxisCrossingEdges]

/-- Number of positive horizontal ray crossings made by a shifted-dual walk, counted as distinct
dual edges. For simple cycles this is the usual parity crossing number. -/
noncomputable def dualWalkPositiveXAxisCrossingCount {u v : DualSquareVertex}
    (w : dualSquareGraph.Walk u v) : ℕ :=
  (dualWalkPositiveXAxisCrossingEdges w).card

/-- Discrete parity definition of "surrounds the origin" for shifted-dual walks. This avoids
mentioning interiors or connected components of `ℝ² \ γ`; the only datum is that the cycle crosses
the positive horizontal ray an odd number of times. -/
def dualWalkSurroundsOriginByParity {u v : DualSquareVertex}
    (w : dualSquareGraph.Walk u v) : Prop :=
  Odd (dualWalkPositiveXAxisCrossingCount w)

/-- For a shifted-dual trail, the existing positive-ray crossing finset count is the same as
counting positive-ray crossing edges in the walk's edge list. -/
theorem dualWalkPositiveXAxisCrossingCount_eq_countP_edges_of_isTrail
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v} (hw : w.IsTrail) :
    dualWalkPositiveXAxisCrossingCount w =
      w.edges.countP isDualPositiveXAxisCrossingEdge := by
  classical
  rw [dualWalkPositiveXAxisCrossingCount, dualWalkPositiveXAxisCrossingEdges]
  rw [walkEdgeFinset]
  rw [show
      {e ∈ (walkEdgeList w).toFinset | ∃ k, e = dualPositiveXAxisCrossingEdge k} =
        {e ∈ (walkEdgeList w).toFinset | isDualPositiveXAxisCrossingDualEdge e = true} by
    ext e
    simp]
  rw [← List.toFinset_filter]
  rw [List.toFinset_card_of_nodup]
  · rw [← List.countP_eq_length_filter]
    unfold walkEdgeList
    rw [List.countP_map]
    change List.countP (fun e : {e // e ∈ w.edges} ↦
        isDualPositiveXAxisCrossingDualEdge
          (⟨e.1, w.edges_subset_edgeSet e.2⟩ : DualSquareEdge)) w.edges.attach =
      w.edges.countP isDualPositiveXAxisCrossingEdge
    simp only [isDualPositiveXAxisCrossingDualEdge_mk]
    exact (List.countP_map (l := w.edges.attach) (f := Subtype.val)
      (p := isDualPositiveXAxisCrossingEdge)).symm.trans (by
        exact congrArg (List.countP isDualPositiveXAxisCrossingEdge)
          (List.attach_map_subtype_val w.edges))
  · exact (nodup_walkEdgeList_of_isTrail hw).filter _

/-- A parity-surrounding normalized positive-axis cycle must also cross the negative horizontal
axis. The proof is purely discrete: a closed walk crosses the lower/upper half-plane cut evenly,
so an odd number of nonnegative x-axis crossings forces an odd, hence nonempty, number of
negative x-axis crossings. -/
theorem exists_negative_dualXAxisCrossingEdge_mem_walkEdgeFinset_of_surroundsOriginByParity
    {k : ℕ}
    {w : dualSquareGraph.Walk (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k)}
    (hw : w.IsCycle) (hparity : dualWalkSurroundsOriginByParity w) :
    ∃ x : ℤ, x < 0 ∧ dualXAxisCrossingEdge x ∈ walkEdgeFinset w := by
  classical
  by_contra hneg
  have htotal_even :
      Even (w.edges.countP (SimpleGraph.Walk.edgeCrossesSetBool dualLowerHalfPlane)) :=
    SimpleGraph.Walk.even_countP_edges_edgeCrossesSet_of_closed dualLowerHalfPlane w
  have hpos_odd_count :
      Odd (w.edges.countP isDualPositiveXAxisCrossingEdge) := by
    rw [← dualWalkPositiveXAxisCrossingCount_eq_countP_edges_of_isTrail hw.isTrail]
    exact hparity
  have hcount_eq :
      w.edges.countP (SimpleGraph.Walk.edgeCrossesSetBool dualLowerHalfPlane) =
        w.edges.countP isDualPositiveXAxisCrossingEdge := by
    apply List.countP_congr
    intro e he
    constructor
    · intro hcut
      have hcut' : SimpleGraph.Walk.edgeCrossesSet dualLowerHalfPlane e :=
        (SimpleGraph.Walk.edgeCrossesSetBool_eq_true dualLowerHalfPlane e).mp hcut
      let ed : DualSquareEdge := ⟨e, w.edges_subset_edgeSet he⟩
      rcases exists_dualXAxisCrossingEdge_of_edgeCrossesDualLowerHalfPlane
          (e := ed) hcut' with
        ⟨x, hxedge⟩
      by_cases hxneg : x < 0
      · have hmem : dualXAxisCrossingEdge x ∈ walkEdgeFinset w := by
          rw [mem_walkEdgeFinset_iff]
          change (dualXAxisCrossingEdge x : Sym2 DualSquareVertex) ∈ w.edges
          have hval : (dualXAxisCrossingEdge x : Sym2 DualSquareVertex) = e := by
            simpa [ed] using (congrArg Subtype.val hxedge).symm
          rw [hval]
          exact he
        exact False.elim (hneg ⟨x, hxneg, hmem⟩)
      · have hxnonneg : 0 ≤ x := by omega
        apply (isDualPositiveXAxisCrossingEdge_eq_true e).mpr
        refine ⟨x.toNat, ?_⟩
        have hxcast : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hxnonneg
        have hxedgepos : dualXAxisCrossingEdge x = dualPositiveXAxisCrossingEdge x.toNat := by
          rw [← hxcast]
          exact dualXAxisCrossingEdge_nat x.toNat
        calc
          e = (dualXAxisCrossingEdge x : Sym2 DualSquareVertex) := by
            simpa [ed] using congrArg Subtype.val hxedge
          _ = (dualPositiveXAxisCrossingEdge x.toNat : Sym2 DualSquareVertex) := by
            exact congrArg Subtype.val hxedgepos
    · intro hpos
      rcases (isDualPositiveXAxisCrossingEdge_eq_true e).mp hpos with ⟨l, rfl⟩
      exact (SimpleGraph.Walk.edgeCrossesSetBool_eq_true dualLowerHalfPlane
        (dualPositiveXAxisCrossingEdge l : Sym2 DualSquareVertex)).mpr
          (edgeCrossesDualLowerHalfPlane_dualPositiveXAxisCrossingEdge l)
  rw [hcount_eq] at htotal_even
  exact Nat.not_even_iff_odd.mpr hpos_odd_count htotal_even

/-- A parity-surrounding walk has at least one positive horizontal ray crossing. -/
theorem dualWalkPositiveXAxisCrossingCount_pos_of_surroundsOriginByParity
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v}
    (h : dualWalkSurroundsOriginByParity w) :
    0 < dualWalkPositiveXAxisCrossingCount w := by
  rcases h with ⟨k, hk⟩
  rw [hk]
  omega

/-- A parity-surrounding walk contains some shifted-dual edge crossing the positive horizontal
ray from the origin. -/
theorem exists_dualPositiveXAxisCrossingEdge_mem_walkEdgeFinset_of_surroundsOriginByParity
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v}
    (h : dualWalkSurroundsOriginByParity w) :
    ∃ k : ℕ, dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset w := by
  classical
  have hnonempty : (dualWalkPositiveXAxisCrossingEdges w).Nonempty :=
    Finset.card_pos.mp (dualWalkPositiveXAxisCrossingCount_pos_of_surroundsOriginByParity h)
  rcases hnonempty with ⟨e, he⟩
  rw [mem_dualWalkPositiveXAxisCrossingEdges] at he
  rcases he with ⟨hew, k, rfl⟩
  exact ⟨k, hew⟩

/-- Circuit-level odd-component selection for the parity Peierls frontier. If the positive-axis
frontier crossings are the edge-disjoint union of the positive-axis crossings made by a finite
family of dual circuits, then one circuit surrounds the origin in the parity sense. -/
theorem exists_dualCircuit_surroundsOriginByParity_of_frontier_decomposition
    {ι : Type*} (m n : ℕ) (ω : EdgeConfiguration 2)
    (s : Finset ι) (circuit : ι → DualCircuit)
    (hdisj :
      (s : Set ι).PairwiseDisjoint fun i ↦ dualWalkPositiveXAxisCrossingEdges (circuit i).walk)
    (hcover :
      s.biUnion (fun i ↦ dualWalkPositiveXAxisCrossingEdges (circuit i).walk) =
        boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω) :
    ∃ i ∈ s, dualWalkSurroundsOriginByParity (circuit i).walk := by
  rcases exists_odd_card_of_frontierPositiveXAxisCrossingEdges_decomposition
      m n ω s (fun i ↦ dualWalkPositiveXAxisCrossingEdges (circuit i).walk) hdisj hcover with
    ⟨i, hi, hodd⟩
  exact ⟨i, hi, by simpa [dualWalkSurroundsOriginByParity, dualWalkPositiveXAxisCrossingCount] using hodd⟩

theorem dualPositiveXAxisCrossingEdge_mem_dualWalkPositiveXAxisCrossingEdges_of_mem
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v} {k : ℕ}
    (hmem : dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset w) :
    dualPositiveXAxisCrossingEdge k ∈ dualWalkPositiveXAxisCrossingEdges w := by
  classical
  rw [mem_dualWalkPositiveXAxisCrossingEdges]
  exact ⟨hmem, ⟨k, rfl⟩⟩

theorem dualPositiveXAxisCrossingEdge_mem_dualWalkPositiveXAxisCrossingEdges_of_startsWith
    {u : DualSquareVertex} {k : ℕ} {w : dualSquareGraph.Walk u u}
    (hw : w.IsCycle) (hstart : dualCycleStartsWithPositiveXAxisCrossing k w) :
    dualPositiveXAxisCrossingEdge k ∈ dualWalkPositiveXAxisCrossingEdges w :=
  dualPositiveXAxisCrossingEdge_mem_dualWalkPositiveXAxisCrossingEdges_of_mem
    (dualPositiveXAxisCrossingEdge_mem_walkEdgeFinset_of_startsWith hw hstart)

/-- Positive-axis crossings of a frontier-supported dual walk are among the positive-axis crossings
of the finite frontier itself. -/
theorem dualWalkPositiveXAxisCrossingEdges_subset_frontierPositiveXAxisCrossingEdges_of_subset
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v}
    {m M : ℕ} {ω : EdgeConfiguration 2}
    (hsubset : (walkEdgeFinset w : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m M ω) :
    (dualWalkPositiveXAxisCrossingEdges w : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierPositiveXAxisCrossingEdges m M ω := by
  intro e he
  have he' : e ∈ dualWalkPositiveXAxisCrossingEdges w := he
  rw [mem_dualWalkPositiveXAxisCrossingEdges] at he'
  change e ∈ boxOpenReachableFrontierPositiveXAxisCrossingEdges m M ω
  rw [mem_boxOpenReachableFrontierPositiveXAxisCrossingEdges]
  exact ⟨hsubset he'.1, he'.2⟩

/-- Cardinal form of
`dualWalkPositiveXAxisCrossingEdges_subset_frontierPositiveXAxisCrossingEdges_of_subset`. -/
theorem dualWalkPositiveXAxisCrossingCount_le_frontierPositiveXAxisCrossingEdges_card_of_subset
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v}
    {m M : ℕ} {ω : EdgeConfiguration 2}
    (hsubset : (walkEdgeFinset w : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m M ω) :
    dualWalkPositiveXAxisCrossingCount w ≤
      (boxOpenReachableFrontierPositiveXAxisCrossingEdges m M ω).card := by
  exact Finset.card_le_card
    (dualWalkPositiveXAxisCrossingEdges_subset_frontierPositiveXAxisCrossingEdges_of_subset
      hsubset)

/-- Reversing a cubic-lattice walk preserves the finite set of traversed edges. -/
theorem walkEdgeFinset_reverse_eq {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) :
    walkEdgeFinset w.reverse = walkEdgeFinset w := by
  classical
  ext e
  rw [mem_walkEdgeFinset_iff, mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_reverse,
    List.mem_reverse]

/-- Rotating a closed cubic-lattice walk preserves the finite set of traversed edges. -/
theorem walkEdgeFinset_rotate_eq {d : ℕ} {u : Cubic d}
    (w : (cubicGraph d).Walk u u) (x : Cubic d) (hx : x ∈ w.support) :
    walkEdgeFinset (w.rotate x hx) = walkEdgeFinset w := by
  classical
  ext e
  rw [mem_walkEdgeFinset_iff, mem_walkEdgeFinset_iff]
  exact (w.rotate_edges x hx).perm.mem_iff

/-- Reversing a shifted-dual walk preserves odd positive-ray crossing parity. -/
theorem dualWalkSurroundsOriginByParity_reverse
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v}
    (h : dualWalkSurroundsOriginByParity w) :
    dualWalkSurroundsOriginByParity w.reverse := by
  simpa [dualWalkSurroundsOriginByParity, dualWalkPositiveXAxisCrossingCount,
    dualWalkPositiveXAxisCrossingEdges, walkEdgeFinset_reverse_eq] using h

/-- Rotating a closed shifted-dual walk preserves odd positive-ray crossing parity. -/
theorem dualWalkSurroundsOriginByParity_rotate
    {u : DualSquareVertex} {w : dualSquareGraph.Walk u u} {x : DualSquareVertex}
    (hx : x ∈ w.support) (h : dualWalkSurroundsOriginByParity w) :
    dualWalkSurroundsOriginByParity (w.rotate x hx) := by
  simpa [dualWalkSurroundsOriginByParity, dualWalkPositiveXAxisCrossingCount,
    dualWalkPositiveXAxisCrossingEdges, walkEdgeFinset_rotate_eq] using h

/-- An odd-parity shifted-dual cycle can be normalized to start with a positive-axis crossing.
The proof is purely discrete: choose a positive crossing edge from the odd crossing finset, rotate
the cycle to its lower endpoint, and reverse the cycle if the first step is the other incident
edge. -/
theorem exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_surroundsOriginByParity
    {u : DualSquareVertex} {w : dualSquareGraph.Walk u u}
    {m n : ℕ} {ω : EdgeConfiguration 2}
    (hw : w.IsCycle)
    (hsubset : (walkEdgeFinset w : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m (m + n) ω)
    (hparity : dualWalkSurroundsOriginByParity w) :
    ∃ k : ℕ, ∃ w' : dualSquareGraph.Walk
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k),
      w'.IsCycle ∧ w'.snd = dualPositiveXAxisUpperVertex k ∧
        (walkEdgeFinset w' : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω ∧
        dualWalkSurroundsOriginByParity w' := by
  classical
  rcases exists_dualPositiveXAxisCrossingEdge_mem_walkEdgeFinset_of_surroundsOriginByParity
      hparity with ⟨k, hkedge⟩
  have hk_edges : (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex) ∈ w.edges :=
    (mem_walkEdgeFinset_iff w (dualPositiveXAxisCrossingEdge k)).mp hkedge
  have hlower : dualPositiveXAxisLowerVertex k ∈ w.support := by
    simpa [dualPositiveXAxisCrossingEdge_coe] using w.fst_mem_support_of_mem_edges hk_edges
  let wr : dualSquareGraph.Walk
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k) :=
    w.rotate (dualPositiveXAxisLowerVertex k) hlower
  have hwr_cycle : wr.IsCycle := hw.rotate hlower
  have hwr_subset : (walkEdgeFinset wr : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m (m + n) ω := by
    intro e he
    apply hsubset
    simpa [wr, walkEdgeFinset_rotate_eq] using he
  have hwr_parity : dualWalkSurroundsOriginByParity wr := by
    simpa [wr] using dualWalkSurroundsOriginByParity_rotate hlower hparity
  have hkedge_wr : dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset wr := by
    simpa [wr, walkEdgeFinset_rotate_eq] using hkedge
  have hk_edges_wr :
      (dualPositiveXAxisCrossingEdge k : Sym2 DualSquareVertex) ∈ wr.edges :=
    (mem_walkEdgeFinset_iff wr (dualPositiveXAxisCrossingEdge k)).mp hkedge_wr
  have hadj_sub : wr.toSubgraph.Adj
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k) := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    simpa [dualPositiveXAxisCrossingEdge_coe] using hk_edges_wr
  have hneighbor : dualPositiveXAxisUpperVertex k ∈
      wr.toSubgraph.neighborSet (dualPositiveXAxisLowerVertex k) := hadj_sub
  rw [hwr_cycle.neighborSet_toSubgraph_endpoint] at hneighbor
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hneighbor
  rcases hneighbor with hnext | hprev
  · exact ⟨k, wr, hwr_cycle, hnext.symm, hwr_subset, hwr_parity⟩
  · let wrev : dualSquareGraph.Walk
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k) := wr.reverse
    have hwrev_cycle : wrev.IsCycle := hwr_cycle.reverse
    have hwrev_subset : (walkEdgeFinset wrev : Set DualSquareEdge) ⊆
        boxOpenReachableFrontierDualEdges m (m + n) ω := by
      intro e he
      apply hwr_subset
      simpa [wrev, walkEdgeFinset_reverse_eq] using he
    have hwrev_parity : dualWalkSurroundsOriginByParity wrev := by
      simpa [wrev] using dualWalkSurroundsOriginByParity_reverse hwr_parity
    have hsnd : wrev.snd = dualPositiveXAxisUpperVertex k := by
      change wr.reverse.snd = dualPositiveXAxisUpperVertex k
      rw [SimpleGraph.Walk.snd_reverse]
      exact hprev.symm
    exact ⟨k, wrev, hwrev_cycle, hsnd, hwrev_subset, hwrev_parity⟩

/-- The finite shifted-dual frontier contains a simple frontier-supported cycle with odd
positive-axis crossing parity. This is the discrete graph-theoretic replacement for the
Jordan-curve selection step: the all-even finite frontier graph and the odd positive-ray crossing
set force one simple cycle to meet the positive ray oddly. -/
theorem exists_dualSquare_isCycle_surroundsOriginByParity_of_frontier
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    ∃ u : DualSquareVertex, ∃ w : dualSquareGraph.Walk u u,
      w.IsCycle ∧
        (walkEdgeFinset w : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω ∧
        dualWalkSurroundsOriginByParity w := by
  classical
  let G := boxOpenReachableFrontierDualGraph m (m + n) ω
  let X : Finset (Sym2 DualSquareVertex) :=
    (boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω).map
      dualSquareEdgeValEmbedding
  have hXedge : ∀ e ∈ X, e ∈ G.edgeSet := by
    intro e he
    change e ∈ (boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω).map
      dualSquareEdgeValEmbedding at he
    rw [Finset.mem_map] at he
    rcases he with ⟨d, hd, rfl⟩
    rw [mem_boxOpenReachableFrontierPositiveXAxisCrossingEdges] at hd
    change (d : Sym2 DualSquareVertex) ∈
      (boxOpenReachableFrontierDualGraph m (m + n) ω).edgeSet
    rw [mem_boxOpenReachableFrontierDualGraph_edgeSet_iff]
    exact ⟨d.property, hd.1⟩
  have hXodd : Odd X.card := by
    change Odd (((boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω).map
      dualSquareEdgeValEmbedding).card)
    rw [Finset.card_map]
    exact boxOpenReachableFrontierPositiveXAxisCrossingEdges_odd m n ω
  rcases SimpleGraph.exists_isCycle_odd_card_filter_of_odd_edge_finset
      G (boxOpenReachableFrontierDualGraph_support_finite m (m + n) ω)
      (even_degree_boxOpenReachableFrontierDualGraph m (m + n) ω) X hXedge hXodd with
    ⟨u, wG, hwGcycle, hodd⟩
  let w : dualSquareGraph.Walk u u := boxOpenReachableFrontierDualGraphWalk wG
  have hwcycle : w.IsCycle :=
    hwGcycle.mapLe (boxOpenReachableFrontierDualGraph_le_dualSquareGraph m (m + n) ω)
  have hsubset : (walkEdgeFinset w : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m (m + n) ω :=
    walkEdgeFinset_boxOpenReachableFrontierDualGraphWalk_subset wG
  have hmap :
      (dualWalkPositiveXAxisCrossingEdges w).map dualSquareEdgeValEmbedding =
        X.filter (fun e ↦ e ∈ wG.edges.toFinset) := by
    ext e
    rw [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [mem_dualWalkPositiveXAxisCrossingEdges] at hd
      have hdfrontier : d ∈ boxOpenReachableFrontierDualEdges m (m + n) ω := hsubset hd.1
      have hdpos : d ∈ boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω := by
        rw [mem_boxOpenReachableFrontierPositiveXAxisCrossingEdges]
        exact ⟨hdfrontier, hd.2⟩
      have hdedge : (d : Sym2 DualSquareVertex) ∈ wG.edges.toFinset := by
        have hdw : (d : Sym2 DualSquareVertex) ∈ w.edges :=
          (mem_walkEdgeFinset_iff w d).mp hd.1
        simpa [w, boxOpenReachableFrontierDualGraphWalk, SimpleGraph.Walk.edges_mapLe_eq_edges]
          using hdw
      have hdX : (d : Sym2 DualSquareVertex) ∈ X := by
        change (d : Sym2 DualSquareVertex) ∈
          (boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω).map
            dualSquareEdgeValEmbedding
        rw [Finset.mem_map]
        exact ⟨d, hdpos, rfl⟩
      exact ⟨hdX, hdedge⟩
    · rintro ⟨heX, hewG⟩
      change e ∈ (boxOpenReachableFrontierPositiveXAxisCrossingEdges m (m + n) ω).map
        dualSquareEdgeValEmbedding at heX
      rw [Finset.mem_map] at heX
      rcases heX with ⟨d, hdpos, rfl⟩
      refine ⟨d, ?_, rfl⟩
      rw [mem_dualWalkPositiveXAxisCrossingEdges]
      rw [mem_boxOpenReachableFrontierPositiveXAxisCrossingEdges] at hdpos
      have hdwalk : d ∈ walkEdgeFinset w := by
        rw [mem_walkEdgeFinset_iff]
        change (d : Sym2 DualSquareVertex) ∈ w.edges
        simpa [w, boxOpenReachableFrontierDualGraphWalk, SimpleGraph.Walk.edges_mapLe_eq_edges]
          using hewG
      exact ⟨hdwalk, hdpos.2⟩
  have hcount : dualWalkPositiveXAxisCrossingCount w =
      (X.filter (fun e ↦ e ∈ wG.edges.toFinset)).card := by
    rw [dualWalkPositiveXAxisCrossingCount]
    rw [← hmap]
    rw [Finset.card_map]
  refine ⟨u, w, hwcycle, hsubset, ?_⟩
  simpa [dualWalkSurroundsOriginByParity, hcount] using hodd

/-- Normalized form of `exists_dualSquare_isCycle_surroundsOriginByParity_of_frontier`: the
odd-parity cycle is rotated so that its first edge is Grimmett's positive-axis crossing. -/
theorem exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_surroundsOriginByParity_of_frontier
    (m n : ℕ) (ω : EdgeConfiguration 2) :
    ∃ k : ℕ, ∃ w : dualSquareGraph.Walk
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k),
      w.IsCycle ∧ w.snd = dualPositiveXAxisUpperVertex k ∧
        (walkEdgeFinset w : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω ∧
        dualWalkSurroundsOriginByParity w := by
  rcases exists_dualSquare_isCycle_surroundsOriginByParity_of_frontier m n ω with
    ⟨u, w, hwcycle, hsubset, hparity⟩
  exact exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_surroundsOriginByParity
    hwcycle hsubset hparity

/-- If a walk uses a shifted-dual vertical edge crossing the horizontal axis at a negative
coordinate, then the walk has a support vertex on or to the left of the line `x = -1`. -/
theorem exists_support_left_of_mem_dualXAxisCrossingEdge_of_neg
    {u v : DualSquareVertex} {w : dualSquareGraph.Walk u v} {x : ℤ}
    (hx : x < 0) (hmem : dualXAxisCrossingEdge x ∈ walkEdgeFinset w) :
    ∃ z : DualSquareVertex, z ∈ w.support ∧ z 0 ≤ -1 := by
  have he : (dualXAxisCrossingEdge x : Sym2 DualSquareVertex) ∈ w.edges :=
    (mem_walkEdgeFinset_iff w (dualXAxisCrossingEdge x)).mp hmem
  refine ⟨dualXAxisLowerVertex x, ?_, ?_⟩
  · simpa [dualXAxisCrossingEdge_coe] using w.fst_mem_support_of_mem_edges he
  · have hxle : x ≤ -1 := by omega
    simpa using hxle

/-- A length-`n` shifted-dual simple cycle normalized at one of Grimmett's positive-axis crossing
edges. This is the concrete source-shaped family whose code map should realize
`ρ(n) ≤ n * σ(n - 1)` for surrounding circuits after the planar extraction theorem supplies such
normalized cycles. -/
structure PositiveXAxisMarkedDualCycle (n : ℕ) where
  /-- The positive-axis crossing coordinate used as the `Fin n` mark. -/
  k : ℕ
  /-- A surrounding length-`n` circuit can only use one of the first `n` positive-axis crossings. -/
  k_lt : k < n
  /-- The cycle, rotated so that it starts at the lower endpoint of the marked crossing edge. -/
  walk : dualSquareGraph.Walk (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k)
  /-- The normalized walk is a simple cycle. -/
  isCycle : walk.IsCycle
  /-- The normalized cycle has the length carried by the family index. -/
  length_eq : walk.length = n
  /-- Its first edge is the marked positive-axis crossing edge. -/
  startsWith : walk.snd = dualPositiveXAxisUpperVertex k

namespace PositiveXAxisMarkedDualCycle

/-- Package a shifted-dual simple cycle as a normalized positive-axis marked cycle once it has
already been rotated to start with the positive-axis crossing edge. -/
def ofWalkStartsWith {u : DualSquareVertex} {k n : ℕ}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) (hlen : w.length = n) (hk : k < n)
    (hstart : dualCycleStartsWithPositiveXAxisCrossing k w) :
    PositiveXAxisMarkedDualCycle n := by
  rcases hstart with ⟨hu, hfirst⟩
  subst u
  exact
    { k := k
      k_lt := hk
      walk := w
      isCycle := hw
      length_eq := hlen
      startsWith := hfirst }

/-- Dual-circuit wrapper for `ofWalkStartsWith`, for the simple-cycle case counted by Grimmett.
This is the bridge needed after a planar extraction theorem has rotated a surrounding closed dual
cycle to its positive-axis crossing. -/
def ofDualCircuitStartsWith (c : DualCircuit) (hcycle : c.walk.IsCycle) {k n : ℕ}
    (hlen : c.length = n) (hk : k < n)
    (hstart : dualCycleStartsWithPositiveXAxisCrossing k c.walk) :
    PositiveXAxisMarkedDualCycle n :=
  ofWalkStartsWith c.walk hcycle hlen hk hstart

/-- If a dual walk starting at Grimmett's positive-axis crossing coordinate `k` reaches a dual
vertex on or to the left of the line `x = -1`, then its length is large enough to use `k` as the
`Fin walk.length` mark. This is the coordinate-excursion part of the planar fact that a
positive-axis frontier cycle surrounding the origin has at most one of its length choices before
the marked crossing. -/
theorem positiveXAxisCrossing_k_lt_length_of_mem_support_left {k : ℕ}
    {v : DualSquareVertex}
    (w : dualSquareGraph.Walk (dualPositiveXAxisLowerVertex k) v) {z : DualSquareVertex}
    (hz : z ∈ w.support) (hzleft : z 0 ≤ -1) :
    k < w.length := by
  let p := w.takeUntil z hz
  have hcoord := cubicWalk_start_coord_le_end_add_length p (0 : Fin 2)
  have htake : p.length ≤ w.length := by
    simpa [p] using SimpleGraph.Walk.length_takeUntil_le w hz
  have hcoord' : (k : ℤ) ≤ z 0 + (p.length : ℤ) := by
    simpa [p, dualPositiveXAxisLowerVertex_zero] using hcoord
  have hkcast : ((k : ℕ) : ℤ) + 1 ≤ (p.length : ℤ) := by
    omega
  omega

/-- A normalized positive-axis cycle that also crosses the negative horizontal axis is long enough
for its positive crossing coordinate to be used as Grimmett's finite mark. -/
theorem positiveXAxisCrossing_k_lt_length_of_mem_negative_dualXAxisCrossingEdge {k : ℕ}
    {w : dualSquareGraph.Walk (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k)}
    {x : ℤ} (hx : x < 0) (hmem : dualXAxisCrossingEdge x ∈ walkEdgeFinset w) :
    k < w.length := by
  rcases exists_support_left_of_mem_dualXAxisCrossingEdge_of_neg hx hmem with
    ⟨z, hz, hzleft⟩
  exact positiveXAxisCrossing_k_lt_length_of_mem_support_left w hz hzleft

/-- Odd positive-ray crossing parity gives the length bound needed for Grimmett's finite mark.
This discharges the parity-to-mark step without a topological interior argument. -/
theorem positiveXAxisCrossing_k_lt_length_of_surroundsOriginByParity {k : ℕ}
    {w : dualSquareGraph.Walk (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k)}
    (hw : w.IsCycle) (hparity : dualWalkSurroundsOriginByParity w) :
    k < w.length := by
  rcases exists_negative_dualXAxisCrossingEdge_mem_walkEdgeFinset_of_surroundsOriginByParity
      hw hparity with
    ⟨x, hx, hmem⟩
  exact positiveXAxisCrossing_k_lt_length_of_mem_negative_dualXAxisCrossingEdge hx hmem

/-- Package an already oriented shifted-dual simple cycle as a normalized positive-axis marked
cycle. This is the final local constructor needed once the surrounding-cycle proof gives
`k < walk.length`. -/
def ofWalkSndEq {k : ℕ}
    (w : dualSquareGraph.Walk (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k))
    (hw : w.IsCycle) (hk : k < w.length) (hfirst : w.snd = dualPositiveXAxisUpperVertex k) :
    PositiveXAxisMarkedDualCycle w.length :=
  ofWalkStartsWith w hw rfl hk ⟨rfl, hfirst⟩

/-- The normalized-cycle package satisfies the general positive-axis start predicate. -/
theorem startsWithPositiveXAxisCrossing {n : ℕ} (c : PositiveXAxisMarkedDualCycle n) :
    dualCycleStartsWithPositiveXAxisCrossing c.k c.walk :=
  ⟨rfl, c.startsWith⟩

/-- The marked positive-axis edge occurs in the normalized cycle. -/
theorem markedEdge_mem_walkEdgeFinset {n : ℕ} (c : PositiveXAxisMarkedDualCycle n) :
    dualPositiveXAxisCrossingEdge c.k ∈ walkEdgeFinset c.walk :=
  dualPositiveXAxisCrossingEdge_mem_walkEdgeFinset_of_startsWith c.isCycle
    c.startsWithPositiveXAxisCrossing

/-- The shifted-dual circuit represented by a normalized positive-axis marked cycle. -/
def toDualCircuit {n : ℕ} (c : PositiveXAxisMarkedDualCycle n) : DualCircuit where
  vertex := dualPositiveXAxisLowerVertex c.k
  walk := c.walk
  isCircuit := c.isCycle.isCircuit

@[simp]
theorem toDualCircuit_length {n : ℕ} (c : PositiveXAxisMarkedDualCycle n) :
    c.toDualCircuit.length = n := by
  simp [toDualCircuit, DualCircuit.length, c.length_eq]

/-- The Grimmett code of a normalized positive-axis marked cycle: the crossing coordinate, viewed
as one of at most `n` choices, together with the reconstructible self-avoiding tail word. -/
noncomputable def code {n : ℕ} (c : PositiveXAxisMarkedDualCycle n) :
    PeierlsCircuitCode n :=
  (⟨c.k, c.k_lt⟩,
    cast (by rw [c.length_eq]) (selfAvoidingWalkOfDualCycleTail c.walk c.isCycle))

@[simp]
theorem code_fst {n : ℕ} (c : PositiveXAxisMarkedDualCycle n) :
    c.code.1 = ⟨c.k, c.k_lt⟩ :=
  rfl

@[simp]
theorem code_snd {n : ℕ} (c : PositiveXAxisMarkedDualCycle n) :
    c.code.2 =
      cast (by rw [c.length_eq]) (selfAvoidingWalkOfDualCycleTail c.walk c.isCycle) :=
  rfl

/-- Equality of Grimmett codes recovers the marked positive-axis crossing coordinate. -/
theorem k_eq_of_code_eq {n : ℕ} {c d : PositiveXAxisMarkedDualCycle n}
    (h : c.code = d.code) :
    c.k = d.k := by
  have hfst : c.code.1 = d.code.1 := congrArg Prod.fst h
  simpa using congrArg Fin.val hfst

/-- Equality of Grimmett codes recovers the underlying direction word of the reconstructible
self-avoiding tail. This is the list-level core needed for the final injectivity proof. -/
theorem tail_toList_eq_of_code_eq {n : ℕ} {c d : PositiveXAxisMarkedDualCycle n}
    (h : c.code = d.code) :
    (selfAvoidingWalkOfDualCycleTail c.walk c.isCycle).1.toList =
      (selfAvoidingWalkOfDualCycleTail d.walk d.isCycle).1.toList := by
  have hsnd : c.code.2 = d.code.2 := congrArg Prod.snd h
  have hc : c.code.2.1.toList =
      (selfAvoidingWalkOfDualCycleTail c.walk c.isCycle).1.toList := by
    rw [code_snd]
    exact selfAvoidingWalk_cast_toList (by rw [c.length_eq])
      (selfAvoidingWalkOfDualCycleTail c.walk c.isCycle)
  have hd : d.code.2.1.toList =
      (selfAvoidingWalkOfDualCycleTail d.walk d.isCycle).1.toList := by
    rw [code_snd]
    exact selfAvoidingWalk_cast_toList (by rw [d.length_eq])
      (selfAvoidingWalkOfDualCycleTail d.walk d.isCycle)
  exact hc.symm.trans ((congrArg (fun saw ↦ saw.1.toList) hsnd).trans hd)

/-- Grimmett's positive-axis code is injective on normalized length-`n` shifted-dual simple
cycles: the first coordinate recovers the marked positive-axis crossing, and the second coordinate
reconstructs the remaining tail of the cycle. This is the formal core of the counting estimate
`ρ(n) ≤ n * σ(n - 1)` for any family whose members have first been normalized in this way. -/
theorem code_injective {n : ℕ} :
    Function.Injective (code (n := n)) := by
  intro c d h
  have hkcd := k_eq_of_code_eq h
  have hlist_cd := tail_toList_eq_of_code_eq h
  cases c with
  | mk k hk w hw hlen hstart =>
  cases d with
  | mk l hl w' hw' hlen' hstart' =>
    dsimp at hkcd hlist_cd
    subst l
    cases w with
    | nil => exact False.elim (SimpleGraph.Walk.IsCycle.not_of_nil hw)
    | @cons u v wend hfirst p =>
    cases w' with
    | nil => exact False.elim (SimpleGraph.Walk.IsCycle.not_of_nil hw')
    | @cons u' v' wend' hfirst' p' =>
      simp only [SimpleGraph.Walk.snd_cons] at hstart hstart'
      subst v
      subst v'
      have hp : p = p' := by
        apply SimpleGraph.Walk.ext_support
        have ht := selfAvoidingWalkOfDualCycleTail_copy_eq (SimpleGraph.Walk.cons hfirst p) hw
        have ht' := selfAvoidingWalkOfDualCycleTail_copy_eq (SimpleGraph.Walk.cons hfirst' p') hw'
        have hts := congrArg SimpleGraph.Walk.support ht
        have hts' := congrArg SimpleGraph.Walk.support ht'
        simp [SimpleGraph.Walk.tail_cons, SimpleGraph.Walk.support_copy, cubicWalkFrom_support]
          at hts hts'
        rw [← hts, ← hts']
        exact congrArg (cubicVerticesFrom (dualPositiveXAxisUpperVertex k)) hlist_cd
      subst hp
      rfl

/-- Normalized positive-axis marked cycles inject into Grimmett's code space. -/
noncomputable def codeEmbedding (n : ℕ) :
    PositiveXAxisMarkedDualCycle n ↪ PeierlsCircuitCode n where
  toFun := code
  inj' := code_injective

/-- There are only finitely many normalized positive-axis marked cycles of a fixed length, because
they inject into Grimmett's finite code space `Fin n × σ(n-1)`. -/
noncomputable instance instFintype (n : ℕ) : Fintype (PositiveXAxisMarkedDualCycle n) :=
  Fintype.ofInjective code code_injective

/-- Grimmett's normalized positive-axis circuit count: the number of normalized length-`n`
shifted-dual cycles is at most `n * σ(n - 1)`. -/
theorem card_le_mul_selfAvoidingWalkCount (n : ℕ) :
    Fintype.card (PositiveXAxisMarkedDualCycle n) ≤
      n * selfAvoidingWalkCount 2 (n - 1) := by
  calc
    Fintype.card (PositiveXAxisMarkedDualCycle n) ≤ Fintype.card (PeierlsCircuitCode n) :=
      Fintype.card_le_of_embedding (codeEmbedding n)
    _ = n * selfAvoidingWalkCount 2 (n - 1) := by
      simp [PeierlsCircuitCode, selfAvoidingWalkCount, Fintype.card_prod]

/-- Event that some normalized positive-axis marked cycle of length `n` is open in the shifted
dual configuration. -/
def openEvent (n : ℕ) : Set (EdgeConfiguration 2) :=
  {ω | ∃ c : PositiveXAxisMarkedDualCycle n, c.toDualCircuit.IsOpen ω}

@[simp]
theorem mem_openEvent (n : ℕ) (ω : EdgeConfiguration 2) :
    ω ∈ openEvent n ↔ ∃ c : PositiveXAxisMarkedDualCycle n, c.toDualCircuit.IsOpen ω :=
  Iff.rfl

/-- Peierls finite-family estimate for normalized positive-axis marked cycles. This is the
probabilistic form of Grimmett's `ρ(n) ≤ n * σ(n - 1)` bound for any circuit family that has been
normalized at its positive-axis crossing. -/
theorem bernoulliBondMeasure_real_openEvent_le (p : I) (n : ℕ) :
    (bernoulliBondMeasure 2 p).real (openEvent n) ≤
      ((n * selfAvoidingWalkCount 2 (n - 1) : ℕ) : ℝ) * (1 - (p : ℝ)) ^ n := by
  simpa [openEvent] using
    (bernoulliBondMeasure_real_existsOpenDualCircuit_of_encoding_le
      p (fun c : PositiveXAxisMarkedDualCycle n ↦ c.toDualCircuit)
      (fun c ↦ c.toDualCircuit_length) (codeEmbedding n))

end PositiveXAxisMarkedDualCycle

/-- Direct normalization bridge for an already oriented shifted-dual frontier cycle once the
positive-axis crossing coordinate is known to fit into the cycle length. This is the counting-only
form needed by the parity-crossing proof: odd positive-ray crossing should supply `k < length`
without invoking a topological interior. -/
theorem exists_positiveXAxisMarkedDualCycle_of_cycle_k_lt_length
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (w : dualSquareGraph.Walk
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k))
    (hwcycle : w.IsCycle) (hfirst : w.snd = dualPositiveXAxisUpperVertex k)
    (hsubset : (walkEdgeFinset w : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m (m + n) ω)
    (hklen : k < w.length) :
    ∃ r : ℕ, ∃ c : PositiveXAxisMarkedDualCycle (m + r),
      c.toDualCircuit.IsOpen ω ∧ c.toDualCircuit.AvoidsBoxEdges m ∧
        (walkEdgeFinset c.toDualCircuit.walk : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω := by
  have hmarked : dualPositiveXAxisCrossingEdge k ∈ walkEdgeFinset w :=
    dualPositiveXAxisCrossingEdge_mem_walkEdgeFinset_of_startsWith hwcycle ⟨rfl, hfirst⟩
  have hmk : m ≤ k :=
    le_of_dualPositiveXAxisCrossingEdge_mem_boxOpenReachableFrontierDualEdges
      (m := m) (M := m + n) (ω := ω) (k := k) (Nat.le_add_right m n)
      (hsubset hmarked)
  have hmlen : m ≤ w.length := le_trans hmk (Nat.le_of_lt hklen)
  let c0 : PositiveXAxisMarkedDualCycle w.length :=
    { k := k
      k_lt := hklen
      walk := w
      isCycle := hwcycle
      length_eq := rfl
      startsWith := hfirst }
  have hfrontier :
      (boxOpenReachableFrontierDualEdges m (m + n) ω : Set DualSquareEdge) ⊆
        dualSquareConfiguration ω :=
    boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
      hno
  have hopen : c0.toDualCircuit.IsOpen ω := by
    exact DualCircuit.isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration
      (fun e he ↦ hfrontier (hsubset (by
        simpa [c0, PositiveXAxisMarkedDualCycle.toDualCircuit] using he)))
  have havoid : c0.toDualCircuit.AvoidsBoxEdges m := by
    exact DualCircuit.avoidsBoxEdges_of_walkEdgeFinset_subset_boxOpenReachableFrontierDualEdges
      (Nat.le_add_right m n) (fun e he ↦ hsubset (by
        simpa [c0, PositiveXAxisMarkedDualCycle.toDualCircuit] using he))
  refine ⟨w.length - m, ?_⟩
  have hidx : m + (w.length - m) = w.length := by omega
  rw [hidx]
  refine ⟨c0, hopen, havoid, ?_⟩
  intro e he
  exact hsubset (by
    simpa [c0, PositiveXAxisMarkedDualCycle.toDualCircuit] using he)

/-- Direct normalization bridge for the actual surrounding frontier cycle. If the planar
extraction theorem produces an oriented simple shifted-dual frontier cycle starting with the
positive-axis crossing, and that cycle makes the left excursion around the origin, then it is one
of Grimmett's normalized positive-axis marked cycles of length at least the source-box radius. -/
theorem exists_positiveXAxisMarkedDualCycle_of_cycle_mem_support_left
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (w : dualSquareGraph.Walk
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k))
    (hwcycle : w.IsCycle) (hfirst : w.snd = dualPositiveXAxisUpperVertex k)
    (hsubset : (walkEdgeFinset w : Set DualSquareEdge) ⊆
      boxOpenReachableFrontierDualEdges m (m + n) ω)
    (hleft : ∃ z : DualSquareVertex, z ∈ w.support ∧ z 0 ≤ -1) :
    ∃ r : ℕ, ∃ c : PositiveXAxisMarkedDualCycle (m + r),
      c.toDualCircuit.IsOpen ω ∧ c.toDualCircuit.AvoidsBoxEdges m ∧
        (walkEdgeFinset c.toDualCircuit.walk : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases hleft with ⟨z, hz, hzleft⟩
  have hklen : k < w.length :=
    PositiveXAxisMarkedDualCycle.positiveXAxisCrossing_k_lt_length_of_mem_support_left
      w hz hzleft
  exact exists_positiveXAxisMarkedDualCycle_of_cycle_k_lt_length
    hno w hwcycle hfirst hsubset hklen

/-- Conditional final normalization bridge for the positive-axis frontier extraction. Once the
remaining planar separation proof shows that the oriented frontier cycle makes the left excursion
around the source box, the already-proved edge-connectivity bridge yields a Grimmett-normalized
positive-axis marked cycle of length at least `m`, open in the shifted-dual configuration and
supported by the finite frontier. -/
theorem exists_positiveXAxisMarkedDualCycle_of_isEdgeReachable_two_of_mem_support_left
    {m n k : ℕ} {ω : EdgeConfiguration 2}
    (hno : ω ∉ boxReachesOutsideBoxAtScaleEvent m n)
    (hadj : (boxOpenReachableFrontierDualGraph m (m + n) ω).Adj
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k))
    (h2 : (boxOpenReachableFrontierDualGraph m (m + n) ω).IsEdgeReachable 2
      (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k))
    (hleft : ∀ {w : dualSquareGraph.Walk
        (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k)},
      w.IsCycle → w.snd = dualPositiveXAxisUpperVertex k →
        (walkEdgeFinset w : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω →
        ∃ z : DualSquareVertex, z ∈ w.support ∧ z 0 ≤ -1) :
    ∃ r : ℕ, ∃ c : PositiveXAxisMarkedDualCycle (m + r),
      c.toDualCircuit.IsOpen ω ∧ c.toDualCircuit.AvoidsBoxEdges m ∧
        (walkEdgeFinset c.toDualCircuit.walk : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges m (m + n) ω := by
  rcases exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two
      hadj h2 with ⟨w, hwcycle, hfirst, hsubset⟩
  exact exists_positiveXAxisMarkedDualCycle_of_cycle_mem_support_left
    hno w hwcycle hfirst hsubset (hleft hwcycle hfirst hsubset)

/-- A Grimmett code for a shifted-dual simple cycle with an explicitly chosen mark. Later, the
mark will be the source-specific crossing of the positive ray used in the proof of
`ρ(n) ≤ n σ(n - 1)`. -/
noncomputable def peierlsCircuitCodeOfMarkedDualCycle {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) (mark : Fin w.length) :
    PeierlsCircuitCode w.length :=
  (mark, selfAvoidingWalkOfDualCycleTail w hw)

/-- A canonical Grimmett code for a shifted-dual simple cycle, marking its first edge. The eventual
`ρ(n) ≤ n σ(n - 1)` injection will refine this by choosing the edge that crosses a prescribed
half-line; this constructor records the already-formalized tail-to-self-avoiding-walk step. -/
noncomputable def peierlsCircuitCodeOfDualCycle {u : DualSquareVertex}
    (w : dualSquareGraph.Walk u u) (hw : w.IsCycle) : PeierlsCircuitCode w.length :=
  peierlsCircuitCodeOfMarkedDualCycle w hw ⟨0, by
      have h3 : 3 ≤ w.length := hw.three_le_length
      omega⟩

/-- The number of Grimmett Peierls circuit codes is exactly `n * σ(n - 1)`. -/
theorem peierlsCircuitCode_card (n : ℕ) :
    Fintype.card (PeierlsCircuitCode n) = n * selfAvoidingWalkCount 2 (n - 1) := by
  simp [PeierlsCircuitCode, selfAvoidingWalkCount, Fintype.card_prod]

/-- A code-indexed per-circuit box-event version of the remaining Peierls geometry. This is the
sharpest current interface for the unfinished planar geometry: decode relevant closed dual
circuits from Grimmett's codes, prove each decoded circuit avoids the bonds of `B(N)` whenever its
length is at least `N`, and prove the box separation implication. -/
structure PlanarPeierlsCodedBoxCircuitGeometry where
  /-- Which Grimmett codes decode to relevant shifted-dual circuits of length `n`. -/
  relevant : ∀ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each length. -/
  finite : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code}
  /-- The shifted-dual circuit decoded from a relevant Grimmett code. -/
  circuit : ∀ n, {code : PeierlsCircuitCode n // relevant n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ n (code : {code : PeierlsCircuitCode n // relevant n code}),
    (circuit n code).length = n
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n →
    ∀ code : {code : PeierlsCircuitCode n // relevant n code},
      (circuit n code).AvoidsBoxEdges N
  /-- The geometric implication in Grimmett's proof for the source box event `G_N`: if every bond
  of `B(N)` is open and no relevant closed dual-circuit tail occurs, then the origin is in an
  infinite open cluster. -/
  infinite_subset : ∀ N,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (encodedOpenDualCircuitTail circuit N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsCodedBoxCircuitGeometry

/-- Coded per-circuit box Peierls geometry supplies per-circuit box Peierls geometry by using
subtype projection as Grimmett's `ρ(n) ≤ n * σ(n - 1)` encoding. -/
noncomputable def toPlanarPeierlsBoxCircuitGeometry
    (G : PlanarPeierlsCodedBoxCircuitGeometry) :
    PlanarPeierlsBoxCircuitGeometry where
  β := fun n ↦ {code : PeierlsCircuitCode n // G.relevant n code}
  finite := G.finite
  circuits := G.circuit
  length_eq := G.length_eq
  encode := fun n ↦
    ⟨Subtype.val, fun a b h ↦ Subtype.ext h⟩
  circuit_avoids_box := by
    intro N n hn code
    exact G.circuit_avoids_box N n hn code
  infinite_subset := by
    intro N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.infinite_subset N

/-- Coded per-circuit box Peierls geometry supplies box-event Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxGeometry (G : PlanarPeierlsCodedBoxCircuitGeometry) :
    PlanarPeierlsBoxGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsBoxGeometry

/-- Coded per-circuit box Peierls geometry supplies support-level Peierls geometry. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsCodedBoxCircuitGeometry) :
    PlanarPeierlsSupportGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsSupportGeometry

/-- Coded per-circuit box Peierls geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsCodedBoxCircuitGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsGeometry

/-- The coded per-circuit box Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsCodedBoxCircuitGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The coded per-circuit box Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsCodedBoxCircuitGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsCodedBoxCircuitGeometry

/-- A source-shaped refinement of the per-circuit box-event Peierls geometry. This splits the
final separation implication exactly as in Grimmett's proof: if no relevant closed dual circuit
occurs, some vertex of `B(N)` has an infinite open cluster; if all bonds of `B(N)` are open, that
infinite cluster connects to the origin. -/
structure PlanarPeierlsBoxSeparationGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n → ∀ b : β n, (circuits n b).AvoidsBoxEdges N
  /-- Planar separation: if no relevant closed dual circuit in the tail occurs, then some vertex
  of `B(N)` has an infinite open cluster. -/
  no_tail_subset_box_vertex_infinite : ∀ N,
    (encodedOpenDualCircuitTail circuits N)ᶜ ⊆ boxVertexInfiniteOpenClusterEvent N
  /-- Box connectivity: if every bond of `B(N)` is open and some vertex of the box has an infinite
  open cluster, then the origin has an infinite open cluster. -/
  box_open_vertex_infinite_subset_origin : ∀ N,
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        boxVertexInfiniteOpenClusterEvent N ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsBoxSeparationGeometry

/-- The separated box Peierls package supplies the per-circuit box Peierls package by composing
the two source separation steps. -/
noncomputable def toPlanarPeierlsBoxCircuitGeometry
    (G : PlanarPeierlsBoxSeparationGeometry) :
    PlanarPeierlsBoxCircuitGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  circuit_avoids_box := G.circuit_avoids_box
  infinite_subset := by
    intro N
    exact openBox_inter_tail_compl_subset_origin_infinite_of_box_vertex G.circuits N
      (G.no_tail_subset_box_vertex_infinite N) (G.box_open_vertex_infinite_subset_origin N)

/-- The separated box Peierls package supplies box-event Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxGeometry (G : PlanarPeierlsBoxSeparationGeometry) :
    PlanarPeierlsBoxGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsBoxGeometry

/-- The separated box Peierls package supplies support-level Peierls geometry. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsBoxSeparationGeometry) :
    PlanarPeierlsSupportGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsSupportGeometry

/-- The separated box Peierls package supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsBoxSeparationGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsGeometry

/-- The separated box Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsBoxSeparationGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The separated box Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsBoxSeparationGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsBoxSeparationGeometry

/-- A code-indexed version of the separated box-event Peierls geometry. This is the most
source-facing current interface: relevant closed dual circuits are decoded from Grimmett's
marked-edge/self-avoiding-walk codes, each circuit avoids the box it surrounds, absence of such a
circuit gives an infinite open cluster from some box vertex, and the box-open event connects that
cluster to the origin. -/
structure PlanarPeierlsCodedBoxSeparationGeometry where
  /-- Which Grimmett codes decode to relevant shifted-dual circuits of length `n`. -/
  relevant : ∀ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each length. -/
  finite : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code}
  /-- The shifted-dual circuit decoded from a relevant Grimmett code. -/
  circuit : ∀ n, {code : PeierlsCircuitCode n // relevant n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ n (code : {code : PeierlsCircuitCode n // relevant n code}),
    (circuit n code).length = n
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n →
    ∀ code : {code : PeierlsCircuitCode n // relevant n code},
      (circuit n code).AvoidsBoxEdges N
  /-- Planar separation: if no relevant closed dual circuit in the tail occurs, then some vertex
  of `B(N)` has an infinite open cluster. -/
  no_tail_subset_box_vertex_infinite : ∀ N,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    (encodedOpenDualCircuitTail circuit N)ᶜ ⊆ boxVertexInfiniteOpenClusterEvent N
  /-- Box connectivity: if every bond of `B(N)` is open and some vertex of the box has an infinite
  open cluster, then the origin has an infinite open cluster. -/
  box_open_vertex_infinite_subset_origin : ∀ N,
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        boxVertexInfiniteOpenClusterEvent N ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsCodedBoxSeparationGeometry

/-- Coded separated box Peierls geometry supplies separated box Peierls geometry by using subtype
projection as Grimmett's `ρ(n) ≤ n * σ(n - 1)` encoding. -/
noncomputable def toPlanarPeierlsBoxSeparationGeometry
    (G : PlanarPeierlsCodedBoxSeparationGeometry) :
    PlanarPeierlsBoxSeparationGeometry where
  β := fun n ↦ {code : PeierlsCircuitCode n // G.relevant n code}
  finite := G.finite
  circuits := G.circuit
  length_eq := G.length_eq
  encode := fun n ↦
    ⟨Subtype.val, fun a b h ↦ Subtype.ext h⟩
  circuit_avoids_box := by
    intro N n hn code
    exact G.circuit_avoids_box N n hn code
  no_tail_subset_box_vertex_infinite := by
    intro N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.no_tail_subset_box_vertex_infinite N
  box_open_vertex_infinite_subset_origin := G.box_open_vertex_infinite_subset_origin

/-- Coded separated box Peierls geometry supplies per-circuit box Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxCircuitGeometry
    (G : PlanarPeierlsCodedBoxSeparationGeometry) :
    PlanarPeierlsBoxCircuitGeometry :=
  G.toPlanarPeierlsBoxSeparationGeometry.toPlanarPeierlsBoxCircuitGeometry

/-- Coded separated box Peierls geometry supplies box-event Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxGeometry (G : PlanarPeierlsCodedBoxSeparationGeometry) :
    PlanarPeierlsBoxGeometry :=
  G.toPlanarPeierlsBoxSeparationGeometry.toPlanarPeierlsBoxGeometry

/-- Coded separated box Peierls geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsCodedBoxSeparationGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxSeparationGeometry.toPlanarPeierlsGeometry

/-- The coded separated box Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsCodedBoxSeparationGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The coded separated box Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsCodedBoxSeparationGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsCodedBoxSeparationGeometry

/-- A box-event Peierls package whose final planar separation field has exactly the outside-tail
shape needed by the proved connector/path-surgery lemma. This removes the separate abstract
box-connectivity field from `PlanarPeierlsBoxSeparationGeometry`: the only remaining separation
obligation is to show that absence of a relevant closed dual circuit gives arbitrarily long open
paths that start in `B(N)` and whose tails avoid `B(N)`. -/
structure PlanarPeierlsBoxOutsideTailsGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n → ∀ b : β n, (circuits n b).AvoidsBoxEdges N
  /-- Planar separation in the direct outside-tail form used by the concrete box connector. -/
  no_tail_subset_box_vertex_outside_tails : ∀ N,
    (encodedOpenDualCircuitTail circuits N)ᶜ ⊆ boxVertexOutsideTailsEvent N

namespace PlanarPeierlsBoxOutsideTailsGeometry

/-- The outside-tail package supplies the per-circuit box Peierls package by using the concrete
box connector to prove the final `G_N ∩ F_Nᶜ` implication. -/
noncomputable def toPlanarPeierlsBoxCircuitGeometry
    (G : PlanarPeierlsBoxOutsideTailsGeometry) :
    PlanarPeierlsBoxCircuitGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  circuit_avoids_box := G.circuit_avoids_box
  infinite_subset := by
    intro N
    exact openBox_inter_tail_compl_subset_origin_infinite_of_box_vertex_outside_tails
      G.circuits N (G.no_tail_subset_box_vertex_outside_tails N)

/-- The outside-tail package supplies source-faithful box-event Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxGeometry (G : PlanarPeierlsBoxOutsideTailsGeometry) :
    PlanarPeierlsBoxGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsBoxGeometry

/-- The outside-tail package supplies support-level Peierls geometry. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsBoxOutsideTailsGeometry) :
    PlanarPeierlsSupportGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsSupportGeometry

/-- The outside-tail package supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsBoxOutsideTailsGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxCircuitGeometry.toPlanarPeierlsGeometry

/-- The outside-tail package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsBoxOutsideTailsGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The outside-tail package supplies the final input package used by the public Theorem 1.10
reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsBoxOutsideTailsGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsBoxOutsideTailsGeometry

/-- A code-indexed version of the outside-tail box-event Peierls package. This is now the sharpest
source-facing interface before the actual planar separation theorem: relevant circuits are decoded
from Grimmett's marked-edge/self-avoiding-walk codes, each avoids the box it surrounds, and absence
of such circuits gives the direct outside-tail open-path event from `B(N)`. -/
structure PlanarPeierlsCodedBoxOutsideTailsGeometry where
  /-- Which Grimmett codes decode to relevant shifted-dual circuits of length `n`. -/
  relevant : ∀ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each length. -/
  finite : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code}
  /-- The shifted-dual circuit decoded from a relevant Grimmett code. -/
  circuit : ∀ n, {code : PeierlsCircuitCode n // relevant n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ n (code : {code : PeierlsCircuitCode n // relevant n code}),
    (circuit n code).length = n
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n →
    ∀ code : {code : PeierlsCircuitCode n // relevant n code},
      (circuit n code).AvoidsBoxEdges N
  /-- Planar separation in the direct outside-tail form used by the concrete box connector. -/
  no_tail_subset_box_vertex_outside_tails : ∀ N,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    (encodedOpenDualCircuitTail circuit N)ᶜ ⊆ boxVertexOutsideTailsEvent N

namespace PlanarPeierlsCodedBoxOutsideTailsGeometry

/-- Coded outside-tail geometry supplies outside-tail geometry by using subtype projection as
Grimmett's `ρ(n) ≤ n * σ(n - 1)` encoding. -/
noncomputable def toPlanarPeierlsBoxOutsideTailsGeometry
    (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) :
    PlanarPeierlsBoxOutsideTailsGeometry where
  β := fun n ↦ {code : PeierlsCircuitCode n // G.relevant n code}
  finite := G.finite
  circuits := G.circuit
  length_eq := G.length_eq
  encode := fun n ↦
    ⟨Subtype.val, fun a b h ↦ Subtype.ext h⟩
  circuit_avoids_box := by
    intro N n hn code
    exact G.circuit_avoids_box N n hn code
  no_tail_subset_box_vertex_outside_tails := by
    intro N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.no_tail_subset_box_vertex_outside_tails N

/-- Coded outside-tail geometry supplies per-circuit box Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxCircuitGeometry
    (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) :
    PlanarPeierlsBoxCircuitGeometry :=
  G.toPlanarPeierlsBoxOutsideTailsGeometry.toPlanarPeierlsBoxCircuitGeometry

/-- Coded outside-tail geometry supplies source-faithful box-event Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxGeometry
    (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) :
    PlanarPeierlsBoxGeometry :=
  G.toPlanarPeierlsBoxOutsideTailsGeometry.toPlanarPeierlsBoxGeometry

/-- Coded outside-tail geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry
    (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxOutsideTailsGeometry.toPlanarPeierlsGeometry

/-- The coded outside-tail package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The coded outside-tail package supplies the final input package used by the public Theorem
1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsCodedBoxOutsideTailsGeometry

/-- A box-exit Peierls package whose final planar separation field says that absence of relevant
closed dual circuits gives open self-avoiding paths from `B(N)` to outside every larger box
`B(N+n)`. The proved last-visit trimming lemma converts this natural finite-box separation output
to the outside-tail package. -/
structure PlanarPeierlsBoxExitGeometry where
  /-- The finite family of relevant shifted-dual circuits of each length. -/
  β : ℕ → Type
  /-- Each length family is finite. -/
  finite : ∀ n, Fintype (β n)
  /-- The relevant shifted-dual circuits, indexed by length. -/
  circuits : ∀ n, β n → DualCircuit
  /-- The length index agrees with the bundled circuit length. -/
  length_eq : ∀ n (b : β n), (circuits n b).length = n
  /-- Grimmett's injection `ρ(n) ≤ n * σ(n - 1)`. -/
  encode : ∀ n, β n ↪ Fin n × SelfAvoidingWalk 2 (n - 1)
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n → ∀ b : β n, (circuits n b).AvoidsBoxEdges N
  /-- Planar separation in finite-box exit form. -/
  no_tail_subset_box_reaches_outside : ∀ N,
    (encodedOpenDualCircuitTail circuits N)ᶜ ⊆ boxVertexReachesOutsideBoxEvent N

namespace PlanarPeierlsBoxExitGeometry

/-- The box-exit package supplies the outside-tail package by trimming paths at their last visit
to `B(N)`. -/
noncomputable def toPlanarPeierlsBoxOutsideTailsGeometry
    (G : PlanarPeierlsBoxExitGeometry) :
    PlanarPeierlsBoxOutsideTailsGeometry where
  β := G.β
  finite := G.finite
  circuits := G.circuits
  length_eq := G.length_eq
  encode := G.encode
  circuit_avoids_box := G.circuit_avoids_box
  no_tail_subset_box_vertex_outside_tails := by
    intro N
    exact (G.no_tail_subset_box_reaches_outside N).trans
      (boxVertexReachesOutsideBoxEvent_subset_boxVertexOutsideTailsEvent N)

/-- The box-exit package supplies per-circuit box Peierls geometry. -/
noncomputable def toPlanarPeierlsBoxCircuitGeometry (G : PlanarPeierlsBoxExitGeometry) :
    PlanarPeierlsBoxCircuitGeometry :=
  G.toPlanarPeierlsBoxOutsideTailsGeometry.toPlanarPeierlsBoxCircuitGeometry

/-- The box-exit package supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsBoxExitGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxOutsideTailsGeometry.toPlanarPeierlsGeometry

/-- The box-exit package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsBoxExitGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The box-exit package supplies the final input package used by the public Theorem 1.10
reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsBoxExitGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsBoxExitGeometry

/-- A code-indexed box-exit Peierls package. This is the most natural current target for the
remaining planar proof: decode Grimmett's relevant circuits from `Fin n × σ(n-1)` codes, prove
they avoid the box bonds, and prove that absence of such circuits gives open paths from `B(N)` to
outside every larger box. -/
structure PlanarPeierlsCodedBoxExitGeometry where
  /-- Which Grimmett codes decode to relevant shifted-dual circuits of length `n`. -/
  relevant : ∀ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each length. -/
  finite : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code}
  /-- The shifted-dual circuit decoded from a relevant Grimmett code. -/
  circuit : ∀ n, {code : PeierlsCircuitCode n // relevant n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ n (code : {code : PeierlsCircuitCode n // relevant n code}),
    (circuit n code).length = n
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n →
    ∀ code : {code : PeierlsCircuitCode n // relevant n code},
      (circuit n code).AvoidsBoxEdges N
  /-- Planar separation in finite-box exit form. -/
  no_tail_subset_box_reaches_outside : ∀ N,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    (encodedOpenDualCircuitTail circuit N)ᶜ ⊆ boxVertexReachesOutsideBoxEvent N

namespace PlanarPeierlsCodedBoxExitGeometry

/-- Coded box-exit geometry supplies box-exit geometry by using subtype projection as Grimmett's
`ρ(n) ≤ n * σ(n - 1)` encoding. -/
noncomputable def toPlanarPeierlsBoxExitGeometry
    (G : PlanarPeierlsCodedBoxExitGeometry) :
    PlanarPeierlsBoxExitGeometry where
  β := fun n ↦ {code : PeierlsCircuitCode n // G.relevant n code}
  finite := G.finite
  circuits := G.circuit
  length_eq := G.length_eq
  encode := fun n ↦
    ⟨Subtype.val, fun a b h ↦ Subtype.ext h⟩
  circuit_avoids_box := by
    intro N n hn code
    exact G.circuit_avoids_box N n hn code
  no_tail_subset_box_reaches_outside := by
    intro N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.no_tail_subset_box_reaches_outside N

/-- Coded box-exit geometry supplies outside-tail geometry. -/
noncomputable def toPlanarPeierlsBoxOutsideTailsGeometry
    (G : PlanarPeierlsCodedBoxExitGeometry) :
    PlanarPeierlsBoxOutsideTailsGeometry :=
  G.toPlanarPeierlsBoxExitGeometry.toPlanarPeierlsBoxOutsideTailsGeometry

/-- Coded box-exit geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsCodedBoxExitGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxExitGeometry.toPlanarPeierlsGeometry

/-- The coded box-exit package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsCodedBoxExitGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The coded box-exit package supplies the final input package used by the public Theorem 1.10
reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsCodedBoxExitGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsCodedBoxExitGeometry

/-- A code-indexed frontier-circuit Peierls package. This is the frontier-level target left after
the finite open-reachable cluster construction: when the finite box-exit event fails, the
shifted-dual frontier contains a relevant circuit from Grimmett's code family. The proved
closed-frontier lemmas then make that circuit open, giving the coded box-exit package. -/
structure PlanarPeierlsCodedFrontierGeometry where
  /-- Which Grimmett codes decode to relevant shifted-dual circuits of length `n`. -/
  relevant : ∀ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each length. -/
  finite : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code}
  /-- The shifted-dual circuit decoded from a relevant Grimmett code. -/
  circuit : ∀ n, {code : PeierlsCircuitCode n // relevant n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ n (code : {code : PeierlsCircuitCode n // relevant n code}),
    (circuit n code).length = n
  /-- Each relevant circuit in the tail avoids the box bonds. -/
  circuit_avoids_box : ∀ N n, N ≤ n →
    ∀ code : {code : PeierlsCircuitCode n // relevant n code},
      (circuit n code).AvoidsBoxEdges N
  /-- Frontier extraction: if a finite exit from `B(N)` to outside `B(N+scale)` fails, then some
  relevant circuit of length at least `N` is supported by the shifted-dual frontier of the finite
  open-reachable cluster. -/
  frontier_circuit_of_not_box_reaches_outside : ∀ N scale (ω : EdgeConfiguration 2),
    ω ∉ boxReachesOutsideBoxAtScaleEvent N scale →
      ∃ k : ℕ, ∃ code : {code : PeierlsCircuitCode (N + k) // relevant (N + k) code},
        (walkEdgeFinset (circuit (N + k) code).walk : Set DualSquareEdge) ⊆
          boxOpenReachableFrontierDualEdges N (N + scale) ω

namespace PlanarPeierlsCodedFrontierGeometry

/-- The frontier-circuit package supplies coded box-exit geometry: if no relevant open dual
circuit tail occurs, then every finite box-exit event must occur, since a failed finite exit would
produce a relevant circuit supported on the closed, hence dual-open, frontier. -/
noncomputable def toPlanarPeierlsCodedBoxExitGeometry
    (G : PlanarPeierlsCodedFrontierGeometry) :
    PlanarPeierlsCodedBoxExitGeometry where
  relevant := G.relevant
  finite := G.finite
  circuit := G.circuit
  length_eq := G.length_eq
  circuit_avoids_box := G.circuit_avoids_box
  no_tail_subset_box_reaches_outside := by
    intro N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    intro ω hω
    rw [mem_boxVertexReachesOutsideBoxEvent_iff_forall_scale]
    intro scale
    by_contra hno
    rcases G.frontier_circuit_of_not_box_reaches_outside N scale ω hno with
      ⟨k, code, hsubset⟩
    have hfrontier :
        (boxOpenReachableFrontierDualEdges N (N + scale) ω : Set DualSquareEdge) ⊆
          dualSquareConfiguration ω :=
      boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
        hno
    have hcopen : (G.circuit (N + k) code).IsOpen ω :=
      DualCircuit.isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration
        (fun _ he ↦ hfrontier (hsubset he))
    exact hω ⟨k, code, hcopen⟩

/-- Frontier-circuit geometry supplies box-exit geometry. -/
noncomputable def toPlanarPeierlsBoxExitGeometry
    (G : PlanarPeierlsCodedFrontierGeometry) :
    PlanarPeierlsBoxExitGeometry :=
  G.toPlanarPeierlsCodedBoxExitGeometry.toPlanarPeierlsBoxExitGeometry

/-- Frontier-circuit geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsCodedFrontierGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsCodedBoxExitGeometry.toPlanarPeierlsGeometry

/-- The frontier-circuit package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsCodedFrontierGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The frontier-circuit package supplies the final input package used by the public Theorem 1.10
reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsCodedFrontierGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsCodedFrontierGeometry

/-- A box-indexed code/frontier Peierls package. This removes the artificial requirement that one
global family of relevant Grimmett codes work for all source boxes: for each box scale `N`, the
relevant length-`n` circuits may be a different subtype of `Fin n × σ(n-1)`.

This is the closest current target to Grimmett's finite frontier proof. A failed finite exit from
`B(N)` must produce an `N`-relevant shifted-dual circuit supported on the dual frontier of the
finite open-reachable cluster. The existing closed-frontier lemmas then make that circuit dual-open,
putting it in the box-indexed tail `F_N`. -/
structure PlanarPeierlsBoxIndexedCodedFrontierGeometry where
  /-- Which Grimmett codes decode to circuits relevant to box scale `N` and length `n`. -/
  relevant : ∀ _ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each box scale and length. -/
  finite : ∀ N n, Fintype {code : PeierlsCircuitCode n // relevant N n code}
  /-- The shifted-dual circuit decoded from an `N`-relevant Grimmett code. -/
  circuit : ∀ N n, {code : PeierlsCircuitCode n // relevant N n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ N n (code : {code : PeierlsCircuitCode n // relevant N n code}),
    (circuit N n code).length = n
  /-- Each `N`-relevant circuit in the `F_N` tail avoids the box bonds of `B(N)`. -/
  circuit_avoids_box : ∀ N n, N ≤ n →
    ∀ code : {code : PeierlsCircuitCode n // relevant N n code},
      (circuit N n code).AvoidsBoxEdges N
  /-- Frontier extraction for the source-shaped indexed family: if a finite exit from `B(N)` to
  outside `B(N+scale)` fails, then some `N`-relevant circuit of length at least `N` is supported by
  the shifted-dual frontier of the finite open-reachable cluster. -/
  frontier_circuit_of_not_box_reaches_outside : ∀ N scale (ω : EdgeConfiguration 2),
    ω ∉ boxReachesOutsideBoxAtScaleEvent N scale →
      ∃ k : ℕ,
        ∃ code : {code : PeierlsCircuitCode (N + k) // relevant N (N + k) code},
          (walkEdgeFinset (circuit N (N + k) code).walk : Set DualSquareEdge) ⊆
            boxOpenReachableFrontierDualEdges N (N + scale) ω

namespace PlanarPeierlsBoxIndexedCodedFrontierGeometry

/-- The box-indexed coded-frontier package supplies box-indexed source-shaped Peierls geometry:
per-circuit box avoidance gives `G_N`/`F_N` independence, while a failed finite exit would create
an open dual circuit in `F_N`. -/
noncomputable def toPlanarPeierlsBoxIndexedGeometry
    (G : PlanarPeierlsBoxIndexedCodedFrontierGeometry) :
    PlanarPeierlsBoxIndexedGeometry where
  β := fun N n ↦ {code : PeierlsCircuitCode n // G.relevant N n code}
  finite := G.finite
  circuits := G.circuit
  length_eq := G.length_eq
  encode := fun N n ↦
    ⟨Subtype.val, fun a b h ↦ Subtype.ext h⟩
  independent := by
    intro p N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant N n code} :=
      G.finite N
    have hind : IndepSet (openEdgeSetEvent 2 (peierlsBoxOpenEdges N))
        (encodedOpenDualCircuitTail (fun n ↦ G.circuit N n) N)
        (bernoulliBondMeasure 2 p) :=
      indepSet_openEdgeSetEvent_encodedOpenDualCircuitTail_of_windows p
        (peierlsBoxOpenEdges N) (fun n ↦ G.circuit N n) N (by
          intro M
          exact indepSet_openEdgeSetEvent_encodedOpenDualCircuitWindow_of_disjoint_support p
            (peierlsBoxOpenEdges N) (fun n ↦ G.circuit N n) N M
            (disjoint_encodedOpenDualCircuitWindowPrimalSupport_of_forall
              (peierlsBoxOpenEdges N) (fun n ↦ G.circuit N n) N M (by
                intro k code
                exact G.circuit_avoids_box N (N + (k : ℕ)) (by omega) code)))
    simpa [boxIndexedOpenDualCircuitTail, encodedOpenDualCircuitTail] using hind
  infinite_subset := by
    intro N ω hω
    refine openBox_inter_boxVertexOutsideTailsEvent_subset_origin_infinite N ⟨hω.1, ?_⟩
    refine boxVertexReachesOutsideBoxEvent_subset_boxVertexOutsideTailsEvent N ?_
    rw [mem_boxVertexReachesOutsideBoxEvent_iff_forall_scale]
    intro scale
    by_contra hno
    rcases G.frontier_circuit_of_not_box_reaches_outside N scale ω hno with
      ⟨k, code, hsubset⟩
    have hfrontier :
        (boxOpenReachableFrontierDualEdges N (N + scale) ω : Set DualSquareEdge) ⊆
          dualSquareConfiguration ω :=
      boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
        hno
    have hcopen : (G.circuit N (N + k) code).IsOpen ω :=
      DualCircuit.isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration
        (fun _ he ↦ hfrontier (hsubset he))
    exact hω.2 ⟨k, code, hcopen⟩

/-- The box-indexed coded-frontier package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsBoxIndexedCodedFrontierGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsBoxIndexedGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The box-indexed coded-frontier package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs
    (G : PlanarPeierlsBoxIndexedCodedFrontierGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsBoxIndexedGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsBoxIndexedCodedFrontierGeometry

/-- A box-indexed frontier package indexed directly by Grimmett's normalized positive-axis marked
dual cycles. This is the source-facing version of the coded-frontier target: the count is supplied
by `PositiveXAxisMarkedDualCycle.codeEmbedding`, while the remaining geometric field says that a
failed finite box exit produces a relevant normalized positive-axis circuit supported on the closed
dual frontier. -/
structure PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry where
  /-- Which normalized positive-axis marked cycles are relevant to box scale `N` and length `n`. -/
  relevant : ∀ _ n, PositiveXAxisMarkedDualCycle n → Prop
  /-- The relevant normalized cycles form a finite family for each box scale and length. -/
  finite : ∀ N n, Fintype {c : PositiveXAxisMarkedDualCycle n // relevant N n c}
  /-- Each `N`-relevant normalized cycle in the `F_N` tail avoids the box bonds of `B(N)`. -/
  circuit_avoids_box : ∀ N n, N ≤ n →
    ∀ c : {c : PositiveXAxisMarkedDualCycle n // relevant N n c},
      c.1.toDualCircuit.AvoidsBoxEdges N
  /-- Frontier extraction for the normalized source-shaped family: if a finite exit from `B(N)` to
  outside `B(N+scale)` fails, then some `N`-relevant normalized positive-axis circuit of length at
  least `N` is supported by the shifted-dual frontier of the finite open-reachable cluster. -/
  frontier_circuit_of_not_box_reaches_outside : ∀ N scale (ω : EdgeConfiguration 2),
    ω ∉ boxReachesOutsideBoxAtScaleEvent N scale →
      ∃ k : ℕ,
        ∃ c : {c : PositiveXAxisMarkedDualCycle (N + k) // relevant N (N + k) c},
          (walkEdgeFinset c.1.toDualCircuit.walk : Set DualSquareEdge) ⊆
            boxOpenReachableFrontierDualEdges N (N + scale) ω

namespace PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry

/-- The normalized positive-axis frontier package supplies box-indexed source-shaped Peierls
geometry. The encoding map is exactly Grimmett's positive-axis mark plus self-avoiding tail word. -/
noncomputable def toPlanarPeierlsBoxIndexedGeometry
    (G : PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry) :
    PlanarPeierlsBoxIndexedGeometry where
  β := fun N n ↦ {c : PositiveXAxisMarkedDualCycle n // G.relevant N n c}
  finite := G.finite
  circuits := fun _ _ c ↦ c.1.toDualCircuit
  length_eq := by
    intro N n c
    exact c.1.toDualCircuit_length
  encode := fun _ n ↦
    { toFun := fun c ↦ c.1.code
      inj' := by
        intro c d h
        exact Subtype.ext (PositiveXAxisMarkedDualCycle.code_injective h) }
  independent := by
    intro p N
    letI : ∀ n, Fintype {c : PositiveXAxisMarkedDualCycle n // G.relevant N n c} :=
      G.finite N
    let circuitsN :
        ∀ n, {c : PositiveXAxisMarkedDualCycle n // G.relevant N n c} → DualCircuit :=
      fun _ c ↦ c.1.toDualCircuit
    have hind : IndepSet (openEdgeSetEvent 2 (peierlsBoxOpenEdges N))
        (encodedOpenDualCircuitTail circuitsN N)
        (bernoulliBondMeasure 2 p) :=
      indepSet_openEdgeSetEvent_encodedOpenDualCircuitTail_of_windows p
        (peierlsBoxOpenEdges N) circuitsN N (by
          intro M
          exact indepSet_openEdgeSetEvent_encodedOpenDualCircuitWindow_of_disjoint_support p
            (peierlsBoxOpenEdges N) circuitsN N M
            (disjoint_encodedOpenDualCircuitWindowPrimalSupport_of_forall
              (peierlsBoxOpenEdges N) circuitsN N M (by
                intro k c
                exact G.circuit_avoids_box N (N + (k : ℕ)) (by omega) c)))
    simpa [boxIndexedOpenDualCircuitTail, encodedOpenDualCircuitTail, circuitsN] using hind
  infinite_subset := by
    intro N ω hω
    refine openBox_inter_boxVertexOutsideTailsEvent_subset_origin_infinite N ⟨hω.1, ?_⟩
    refine boxVertexReachesOutsideBoxEvent_subset_boxVertexOutsideTailsEvent N ?_
    rw [mem_boxVertexReachesOutsideBoxEvent_iff_forall_scale]
    intro scale
    by_contra hno
    rcases G.frontier_circuit_of_not_box_reaches_outside N scale ω hno with
      ⟨k, c, hsubset⟩
    have hfrontier :
        (boxOpenReachableFrontierDualEdges N (N + scale) ω : Set DualSquareEdge) ⊆
          dualSquareConfiguration ω :=
      boxOpenReachableFrontierDualEdges_subset_dualSquareConfiguration_of_not_boxReachesOutside
        hno
    have hcopen : c.1.toDualCircuit.IsOpen ω :=
      DualCircuit.isOpen_of_walkEdgeFinset_subset_dualSquareConfiguration
        (fun _ he ↦ hfrontier (hsubset he))
    exact hω.2 ⟨k, c, hcopen⟩

/-- The normalized positive-axis frontier package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsBoxIndexedGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The normalized positive-axis frontier package supplies the final input package used by the
public Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs
    (G : PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsBoxIndexedGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry

/-- The remaining concrete planar extraction target after the finite reachable-cluster frontier
has been built. It asks for exactly the source-facing topological facts still missing from the
Peierls proof: a positive-axis frontier edge that is not a bridge in the finite dual frontier, and
the left excursion showing that the oriented cycle surrounds the source box. -/
structure PlanarPeierlsPositiveAxisFrontierExtraction where
  /-- Failed finite box exit produces a positive-axis frontier edge whose deletion still leaves
  its endpoints connected, and every oriented simple frontier cycle through that edge makes the
  left excursion around the origin. -/
  frontier_edge : ∀ N scale (ω : EdgeConfiguration 2),
    ω ∉ boxReachesOutsideBoxAtScaleEvent N scale →
      ∃ k : ℕ,
        (boxOpenReachableFrontierDualGraph N (N + scale) ω).Adj
          (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k) ∧
        (boxOpenReachableFrontierDualGraph N (N + scale) ω).IsEdgeReachable 2
          (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisUpperVertex k) ∧
        ∀ {w : dualSquareGraph.Walk
            (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k)},
          w.IsCycle → w.snd = dualPositiveXAxisUpperVertex k →
            (walkEdgeFinset w : Set DualSquareEdge) ⊆
              boxOpenReachableFrontierDualEdges N (N + scale) ω →
            ∃ z : DualSquareVertex, z ∈ w.support ∧ z 0 ≤ -1

namespace PlanarPeierlsPositiveAxisFrontierExtraction

/-- The concrete positive-axis extraction target supplies the normalized positive-axis frontier
package consumed by the Peierls probability/counting argument. -/
noncomputable def toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry
    (G : PlanarPeierlsPositiveAxisFrontierExtraction) :
    PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry where
  relevant := fun N _ c ↦ c.toDualCircuit.AvoidsBoxEdges N
  finite := by
    intro N n
    classical
    infer_instance
  circuit_avoids_box := by
    intro N n hn c
    exact c.2
  frontier_circuit_of_not_box_reaches_outside := by
    intro N scale ω hno
    rcases G.frontier_edge N scale ω hno with ⟨k, hadj, h2, hleft⟩
    rcases
      exists_positiveXAxisMarkedDualCycle_of_isEdgeReachable_two_of_mem_support_left
        hno hadj h2 hleft with
      ⟨r, c, _hcopen, hcavoid, hsubset⟩
    refine ⟨r, ⟨c, hcavoid⟩, ?_⟩
    exact hsubset

/-- The positive-axis extraction target proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsPositiveAxisFrontierExtraction) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The positive-axis extraction target supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs
    (G : PlanarPeierlsPositiveAxisFrontierExtraction) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsPositiveAxisFrontierExtraction

/-- A sharper source-facing positive-axis extraction target. This matches Grimmett's construction
more directly than `PlanarPeierlsPositiveAxisFrontierExtraction`: a failed finite exit must produce
one oriented simple frontier cycle, normalized at the positive-axis crossing and making the left
excursion around the origin. -/
structure PlanarPeierlsPositiveAxisFrontierCycleExtraction where
  /-- Failed finite box exit produces the actual surrounding positive-axis frontier cycle. -/
  frontier_cycle : ∀ N scale (ω : EdgeConfiguration 2),
    ω ∉ boxReachesOutsideBoxAtScaleEvent N scale →
      ∃ k : ℕ, ∃ w : dualSquareGraph.Walk
          (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k),
        w.IsCycle ∧ w.snd = dualPositiveXAxisUpperVertex k ∧
          (walkEdgeFinset w : Set DualSquareEdge) ⊆
            boxOpenReachableFrontierDualEdges N (N + scale) ω ∧
          ∃ z : DualSquareVertex, z ∈ w.support ∧ z 0 ≤ -1

namespace PlanarPeierlsPositiveAxisFrontierCycleExtraction

/-- The cycle-extraction target supplies the normalized positive-axis frontier package consumed by
the Peierls probability/counting argument. -/
noncomputable def toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry
    (G : PlanarPeierlsPositiveAxisFrontierCycleExtraction) :
    PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry where
  relevant := fun N _ c ↦ c.toDualCircuit.AvoidsBoxEdges N
  finite := by
    intro N n
    classical
    infer_instance
  circuit_avoids_box := by
    intro N n hn c
    exact c.2
  frontier_circuit_of_not_box_reaches_outside := by
    intro N scale ω hno
    rcases G.frontier_cycle N scale ω hno with
      ⟨k, w, hwcycle, hfirst, hsubset, hleft⟩
    rcases
      exists_positiveXAxisMarkedDualCycle_of_cycle_mem_support_left
        hno w hwcycle hfirst hsubset hleft with
      ⟨r, c, _hcopen, hcavoid, hsubset'⟩
    refine ⟨r, ⟨c, hcavoid⟩, ?_⟩
    exact hsubset'

/-- The cycle-extraction target proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsPositiveAxisFrontierCycleExtraction) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The cycle-extraction target supplies the final input package used by the public Theorem 1.10
reductions. -/
theorem toGrimmettTheorem110Inputs
    (G : PlanarPeierlsPositiveAxisFrontierCycleExtraction) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsPositiveAxisFrontierCycleExtraction

/-- Parity-crossing version of the remaining source-facing Peierls extraction target. This matches
the discrete replacement for the Jordan-curve language: a failed finite exit should yield a simple
frontier cycle, normalized at a positive-axis crossing, whose positive horizontal ray crossing
number is odd. The parity-to-mark-bound bridge is proved above by closed-walk cut parity, so the
only remaining input here is the actual frontier cycle extraction. -/
structure PlanarPeierlsParityFrontierCycleExtraction where
  /-- Failed finite box exit produces a normalized simple frontier cycle with odd positive-ray
  crossing number. -/
  frontier_parity_cycle : ∀ N scale (ω : EdgeConfiguration 2),
    ω ∉ boxReachesOutsideBoxAtScaleEvent N scale →
      ∃ k : ℕ, ∃ w : dualSquareGraph.Walk
          (dualPositiveXAxisLowerVertex k) (dualPositiveXAxisLowerVertex k),
        w.IsCycle ∧ w.snd = dualPositiveXAxisUpperVertex k ∧
          (walkEdgeFinset w : Set DualSquareEdge) ⊆
            boxOpenReachableFrontierDualEdges N (N + scale) ω ∧
          dualWalkSurroundsOriginByParity w

namespace PlanarPeierlsParityFrontierCycleExtraction

/-- The parity-crossing extraction target supplies the normalized positive-axis frontier package
used by the Peierls probability/counting argument. -/
noncomputable def toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry
    (G : PlanarPeierlsParityFrontierCycleExtraction) :
    PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry where
  relevant := fun N _ c ↦ c.toDualCircuit.AvoidsBoxEdges N
  finite := by
    intro N n
    classical
    infer_instance
  circuit_avoids_box := by
    intro N n hn c
    exact c.2
  frontier_circuit_of_not_box_reaches_outside := by
    intro N scale ω hno
    rcases G.frontier_parity_cycle N scale ω hno with
      ⟨k, w, hwcycle, hfirst, hsubset, hparity⟩
    have hklen : k < w.length :=
      PositiveXAxisMarkedDualCycle.positiveXAxisCrossing_k_lt_length_of_surroundsOriginByParity
        hwcycle hparity
    rcases exists_positiveXAxisMarkedDualCycle_of_cycle_k_lt_length
        hno w hwcycle hfirst hsubset hklen with
      ⟨r, c, _hcopen, hcavoid, hsubset'⟩
    exact ⟨r, ⟨c, hcavoid⟩, hsubset'⟩

/-- The parity-crossing extraction target proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsParityFrontierCycleExtraction) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The parity-crossing extraction target supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs
    (G : PlanarPeierlsParityFrontierCycleExtraction) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsParityFrontierCycleExtraction

/-- Concrete parity-crossing frontier extraction. This discharges the former source-facing
geometric placeholder by the finite even-frontier graph and odd positive-ray crossing argument:
no continuous Jordan-curve theorem is used. -/
noncomputable def planarPeierlsParityFrontierCycleExtraction :
    PlanarPeierlsParityFrontierCycleExtraction where
  frontier_parity_cycle := by
    intro N scale ω _hno
    exact
      exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_surroundsOriginByParity_of_frontier
        N scale ω

/-- The concrete parity frontier extraction supplies Grimmett's final Theorem 1.10 input package. -/
theorem grimmettTheorem110Inputs : GrimmettTheorem110Inputs :=
  planarPeierlsParityFrontierCycleExtraction.toGrimmettTheorem110Inputs

/-- Grimmett, Equation (1.12), proved from the concrete parity-frontier Peierls extraction. -/
theorem cubicCriticalProbability_two_bounds :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs grimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), proved from the concrete parity-frontier Peierls extraction. -/
theorem cubicCriticalProbability_pos_lt_one {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs grimmettTheorem110Inputs hd

/-- Compatibility alias for Grimmett, Equation (1.12). -/
theorem cubicCriticalProbability_two_bounds_grimmett :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds

/-- Compatibility alias for Grimmett, Theorem (1.10). -/
theorem cubicCriticalProbability_pos_lt_one_grimmett {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one hd

/-- Finite-decomposition version of the parity frontier target. This packages the exact discrete
replacement for the Jordan-curve step: after a failed finite exit, decompose the finite
shifted-dual frontier into edge-disjoint normalized simple cycles whose positive-ray crossing
sets cover the frontier positive-ray crossings. Since the frontier has odd total crossing parity,
one component cycle has odd crossing parity; closed-walk cut parity then supplies Grimmett's mark
bound. -/
structure PlanarPeierlsParityFrontierCircuitDecomposition where
  /-- Failed finite box exit gives a finite edge-disjoint normalized cycle decomposition of the
  positive-ray part of the finite shifted-dual frontier. -/
  frontier_decomposition : ∀ N scale (ω : EdgeConfiguration 2),
    ω ∉ boxReachesOutsideBoxAtScaleEvent N scale →
      ∃ ι : Type, ∃ s : Finset ι, ∃ k : ι → ℕ,
        ∃ w : (i : ι) →
            dualSquareGraph.Walk
              (dualPositiveXAxisLowerVertex (k i)) (dualPositiveXAxisLowerVertex (k i)),
          (∀ i, i ∈ s →
            (w i).IsCycle ∧ (w i).snd = dualPositiveXAxisUpperVertex (k i) ∧
              (walkEdgeFinset (w i) : Set DualSquareEdge) ⊆
                boxOpenReachableFrontierDualEdges N (N + scale) ω) ∧
          ((s : Set ι).PairwiseDisjoint fun i ↦ dualWalkPositiveXAxisCrossingEdges (w i)) ∧
          s.biUnion (fun i ↦ dualWalkPositiveXAxisCrossingEdges (w i)) =
            boxOpenReachableFrontierPositiveXAxisCrossingEdges N (N + scale) ω

namespace PlanarPeierlsParityFrontierCircuitDecomposition

/-- A finite edge-disjoint normalized cycle decomposition supplies the parity-cycle extraction
interface by selecting an odd crossing component. -/
noncomputable def toPlanarPeierlsParityFrontierCycleExtraction
    (G : PlanarPeierlsParityFrontierCircuitDecomposition) :
    PlanarPeierlsParityFrontierCycleExtraction where
  frontier_parity_cycle := by
    intro N scale ω hno
    rcases G.frontier_decomposition N scale ω hno with
      ⟨ι, s, k, w, hcycles, hdisj, hcover⟩
    rcases exists_odd_card_of_frontierPositiveXAxisCrossingEdges_decomposition
        N scale ω s (fun i ↦ dualWalkPositiveXAxisCrossingEdges (w i)) hdisj hcover with
      ⟨i, hi, hodd⟩
    rcases hcycles i hi with ⟨hwcycle, hfirst, hsubset⟩
    refine ⟨k i, w i, hwcycle, hfirst, hsubset, ?_⟩
    simpa [dualWalkSurroundsOriginByParity, dualWalkPositiveXAxisCrossingCount] using hodd

/-- The finite-decomposition parity target proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv
    (G : PlanarPeierlsParityFrontierCircuitDecomposition) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsParityFrontierCycleExtraction.cubicCriticalProbability_le_one_sub_inv

/-- The finite-decomposition parity target supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs
    (G : PlanarPeierlsParityFrontierCircuitDecomposition) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsParityFrontierCycleExtraction.toGrimmettTheorem110Inputs

end PlanarPeierlsParityFrontierCircuitDecomposition

/-- The stronger edge-connectivity extraction package supplies the sharper cycle-extraction
package by choosing the oriented cycle furnished by the 2-edge-reachability bridge. -/
noncomputable def PlanarPeierlsPositiveAxisFrontierExtraction.toCycleExtraction
    (G : PlanarPeierlsPositiveAxisFrontierExtraction) :
    PlanarPeierlsPositiveAxisFrontierCycleExtraction where
  frontier_cycle := by
    intro N scale ω hno
    rcases G.frontier_edge N scale ω hno with ⟨k, hadj, h2, hleft⟩
    rcases
      exists_dualSquare_isCycle_startsWith_positiveXAxisCrossing_of_isEdgeReachable_two
        hadj h2 with
      ⟨w, hwcycle, hfirst, hsubset⟩
    exact ⟨k, w, hwcycle, hfirst, hsubset, hleft hwcycle hfirst hsubset⟩

/-- A code-indexed box-event version of the remaining Peierls geometry. This is the closest
current interface to Grimmett's proof after (1.18): `G_m` is the event that all bonds of `B(m)` are
open, and the relevant closed dual circuits are indexed directly by the marked-vertex/self-avoiding
walk codes used in the estimate `ρ(n) ≤ n * σ(n - 1)`. -/
structure PlanarPeierlsCodedBoxGeometry where
  /-- Which Grimmett codes decode to relevant shifted-dual circuits of length `n`. -/
  relevant : ∀ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each length. -/
  finite : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code}
  /-- The shifted-dual circuit decoded from a relevant Grimmett code. -/
  circuit : ∀ n, {code : PeierlsCircuitCode n // relevant n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ n (code : {code : PeierlsCircuitCode n // relevant n code}),
    (circuit n code).length = n
  /-- The box-open event `G_N` is disjoint from the primal bonds crossed by each finite
  closed-dual-circuit window. -/
  support_disjoint : ∀ N M,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    Disjoint ((peierlsBoxOpenEdges N : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      ((encodedOpenDualCircuitWindowPrimalSupport circuit N M : Finset (CubicEdge 2)) :
        Set (CubicEdge 2))
  /-- The geometric implication in Grimmett's proof for the source box event `G_N`: if every bond
  of `B(N)` is open and no relevant closed dual-circuit tail occurs, then the origin is in an
  infinite open cluster. -/
  infinite_subset : ∀ N,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    openEdgeSetEvent 2 (peierlsBoxOpenEdges N) ∩
        (encodedOpenDualCircuitTail circuit N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsCodedBoxGeometry

/-- Coded box-event Peierls geometry supplies box-event Peierls geometry by using subtype
projection as Grimmett's `ρ(n) ≤ n * σ(n - 1)` encoding. -/
noncomputable def toPlanarPeierlsBoxGeometry (G : PlanarPeierlsCodedBoxGeometry) :
    PlanarPeierlsBoxGeometry where
  β := fun n ↦ {code : PeierlsCircuitCode n // G.relevant n code}
  finite := G.finite
  circuits := G.circuit
  length_eq := G.length_eq
  encode := fun n ↦
    ⟨Subtype.val, fun a b h ↦ Subtype.ext h⟩
  support_disjoint := by
    intro N M
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.support_disjoint N M
  infinite_subset := by
    intro N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.infinite_subset N

/-- Coded box-event Peierls geometry supplies support-level Peierls geometry. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsCodedBoxGeometry) :
    PlanarPeierlsSupportGeometry :=
  G.toPlanarPeierlsBoxGeometry.toPlanarPeierlsSupportGeometry

/-- Coded box-event Peierls geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsCodedBoxGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsBoxGeometry.toPlanarPeierlsGeometry

/-- The coded box-event Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsCodedBoxGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The coded box-event Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsCodedBoxGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsCodedBoxGeometry

/-- A code-indexed straight-path version of the remaining Peierls geometry. Compared with
`PlanarPeierlsStraightGeometry`, this package no longer assumes an arbitrary encoding map:
the relevant closed dual circuits are indexed directly by Grimmett's codes
`Fin n × SelfAvoidingWalk 2 (n - 1)`, and the encoding used in the count is subtype projection. -/
structure PlanarPeierlsCodedStraightGeometry where
  /-- Which Grimmett codes decode to relevant shifted-dual circuits of length `n`. -/
  relevant : ∀ n, PeierlsCircuitCode n → Prop
  /-- The relevant codes form a finite family for each length. This is automatic for decidable
  predicates, but is kept explicit so the geometry layer can choose its predicate first. -/
  finite : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code}
  /-- The shifted-dual circuit decoded from a relevant Grimmett code. -/
  circuit : ∀ n, {code : PeierlsCircuitCode n // relevant n code} → DualCircuit
  /-- The decoded circuit has the length carried by its code family. -/
  length_eq : ∀ n (code : {code : PeierlsCircuitCode n // relevant n code}),
    (circuit n code).length = n
  /-- The straight finite open path `G_N` is disjoint from the primal bonds crossed by each finite
  closed-dual-circuit window. -/
  support_disjoint : ∀ N M,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    Disjoint ((peierlsStraightOpenPathEdges N : Finset (CubicEdge 2)) : Set (CubicEdge 2))
      ((encodedOpenDualCircuitWindowPrimalSupport circuit N M : Finset (CubicEdge 2)) :
        Set (CubicEdge 2))
  /-- The geometric implication in Grimmett's proof for the concrete straight `G_N`: if the straight
  path is open and no relevant closed dual-circuit tail occurs, then the origin is in an infinite
  open cluster. -/
  infinite_subset : ∀ N,
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // relevant n code} := finite
    openEdgeSetEvent 2 (peierlsStraightOpenPathEdges N) ∩
        (encodedOpenDualCircuitTail circuit N)ᶜ ⊆
      {ω : EdgeConfiguration 2 | hasInfiniteOpenCluster 2 ω}

namespace PlanarPeierlsCodedStraightGeometry

/-- Coded straight Peierls geometry supplies straight Peierls geometry by using subtype projection
as Grimmett's `ρ(n) ≤ n * σ(n - 1)` encoding. -/
noncomputable def toPlanarPeierlsStraightGeometry (G : PlanarPeierlsCodedStraightGeometry) :
    PlanarPeierlsStraightGeometry where
  β := fun n ↦ {code : PeierlsCircuitCode n // G.relevant n code}
  finite := G.finite
  circuits := G.circuit
  length_eq := G.length_eq
  encode := fun n ↦
    ⟨Subtype.val, fun a b h ↦ Subtype.ext h⟩
  support_disjoint := by
    intro N M
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.support_disjoint N M
  infinite_subset := by
    intro N
    letI : ∀ n, Fintype {code : PeierlsCircuitCode n // G.relevant n code} := G.finite
    exact G.infinite_subset N

/-- Coded straight Peierls geometry supplies support-level Peierls geometry. -/
noncomputable def toPlanarPeierlsSupportGeometry (G : PlanarPeierlsCodedStraightGeometry) :
    PlanarPeierlsSupportGeometry :=
  G.toPlanarPeierlsStraightGeometry.toPlanarPeierlsSupportGeometry

/-- Coded straight Peierls geometry supplies tail-level Peierls geometry. -/
noncomputable def toPlanarPeierlsGeometry (G : PlanarPeierlsCodedStraightGeometry) :
    PlanarPeierlsGeometry :=
  G.toPlanarPeierlsStraightGeometry.toPlanarPeierlsGeometry

/-- The coded straight Peierls package proves Grimmett's planar upper bound
`p_c(2) ≤ 1 - 1/λ(2)`. -/
theorem cubicCriticalProbability_le_one_sub_inv (G : PlanarPeierlsCodedStraightGeometry) :
    cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  G.toPlanarPeierlsGeometry.cubicCriticalProbability_le_one_sub_inv

/-- The coded straight Peierls package supplies the final input package used by the public
Theorem 1.10 reductions. -/
theorem toGrimmettTheorem110Inputs (G : PlanarPeierlsCodedStraightGeometry) :
    GrimmettTheorem110Inputs :=
  G.toPlanarPeierlsGeometry.toGrimmettTheorem110Inputs

end PlanarPeierlsCodedStraightGeometry

/-- Grimmett, Equation (1.12), reduced to the source-shaped planar Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsGeometry
    (G : PlanarPeierlsGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the source-shaped planar Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsGeometry
    (G : PlanarPeierlsGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the box-indexed planar Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxIndexedGeometry
    (G : PlanarPeierlsBoxIndexedGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the box-indexed planar Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxIndexedGeometry
    (G : PlanarPeierlsBoxIndexedGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the box-indexed coded-frontier Peierls package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxIndexedCodedFrontierGeometry
    (G : PlanarPeierlsBoxIndexedCodedFrontierGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the box-indexed coded-frontier Peierls package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxIndexedCodedFrontierGeometry
    (G : PlanarPeierlsBoxIndexedCodedFrontierGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the box-indexed normalized positive-axis frontier
Peierls package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxIndexedPositiveAxisFrontierGeometry
    (G : PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the box-indexed normalized positive-axis frontier Peierls
package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxIndexedPositiveAxisFrontierGeometry
    (G : PlanarPeierlsBoxIndexedPositiveAxisFrontierGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the concrete positive-axis frontier extraction target. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsPositiveAxisFrontierExtraction
    (G : PlanarPeierlsPositiveAxisFrontierExtraction) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the concrete positive-axis frontier extraction target. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsPositiveAxisFrontierExtraction
    (G : PlanarPeierlsPositiveAxisFrontierExtraction) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the concrete positive-axis frontier cycle-extraction
target. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsPositiveAxisFrontierCycleExtraction
    (G : PlanarPeierlsPositiveAxisFrontierCycleExtraction) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the concrete positive-axis frontier cycle-extraction
target. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsPositiveAxisFrontierCycleExtraction
    (G : PlanarPeierlsPositiveAxisFrontierCycleExtraction) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the parity-crossing positive-axis frontier cycle
extraction target. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsParityFrontierCycleExtraction
    (G : PlanarPeierlsParityFrontierCycleExtraction) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the parity-crossing positive-axis frontier cycle
extraction target. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsParityFrontierCycleExtraction
    (G : PlanarPeierlsParityFrontierCycleExtraction) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the finite parity frontier circuit-decomposition
target. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsParityFrontierCircuitDecomposition
    (G : PlanarPeierlsParityFrontierCircuitDecomposition) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the finite parity frontier circuit-decomposition
target. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsParityFrontierCircuitDecomposition
    (G : PlanarPeierlsParityFrontierCircuitDecomposition) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the finite-window Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsWindowGeometry
    (G : PlanarPeierlsWindowGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the finite-window Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsWindowGeometry
    (G : PlanarPeierlsWindowGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the support-level Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsSupportGeometry
    (G : PlanarPeierlsSupportGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the support-level Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsSupportGeometry
    (G : PlanarPeierlsSupportGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the source-faithful box-event Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxGeometry
    (G : PlanarPeierlsBoxGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the source-faithful box-event Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxGeometry
    (G : PlanarPeierlsBoxGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the per-circuit box-event Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxCircuitGeometry
    (G : PlanarPeierlsBoxCircuitGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the per-circuit box-event Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxCircuitGeometry
    (G : PlanarPeierlsBoxCircuitGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the straight-path Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsStraightGeometry
    (G : PlanarPeierlsStraightGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the straight-path Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsStraightGeometry
    (G : PlanarPeierlsStraightGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the coded box-event Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsCodedBoxGeometry
    (G : PlanarPeierlsCodedBoxGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the coded box-event Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedBoxGeometry
    (G : PlanarPeierlsCodedBoxGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the coded per-circuit box-event Peierls geometry
package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsCodedBoxCircuitGeometry
    (G : PlanarPeierlsCodedBoxCircuitGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the coded per-circuit box-event Peierls geometry
package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedBoxCircuitGeometry
    (G : PlanarPeierlsCodedBoxCircuitGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the separated box-event Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxSeparationGeometry
    (G : PlanarPeierlsBoxSeparationGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the separated box-event Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxSeparationGeometry
    (G : PlanarPeierlsBoxSeparationGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the coded separated box-event Peierls geometry
package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsCodedBoxSeparationGeometry
    (G : PlanarPeierlsCodedBoxSeparationGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the coded separated box-event Peierls geometry
package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedBoxSeparationGeometry
    (G : PlanarPeierlsCodedBoxSeparationGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the outside-tail box-event Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxOutsideTailsGeometry
    (G : PlanarPeierlsBoxOutsideTailsGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the outside-tail box-event Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxOutsideTailsGeometry
    (G : PlanarPeierlsBoxOutsideTailsGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the coded outside-tail box-event Peierls geometry
package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsCodedBoxOutsideTailsGeometry
    (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the coded outside-tail box-event Peierls geometry
package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedBoxOutsideTailsGeometry
    (G : PlanarPeierlsCodedBoxOutsideTailsGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the box-exit Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsBoxExitGeometry
    (G : PlanarPeierlsBoxExitGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the box-exit Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsBoxExitGeometry
    (G : PlanarPeierlsBoxExitGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the coded box-exit Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsCodedBoxExitGeometry
    (G : PlanarPeierlsCodedBoxExitGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the coded box-exit Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedBoxExitGeometry
    (G : PlanarPeierlsCodedBoxExitGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the coded frontier-circuit Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsCodedFrontierGeometry
    (G : PlanarPeierlsCodedFrontierGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the coded frontier-circuit Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedFrontierGeometry
    (G : PlanarPeierlsCodedFrontierGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

/-- Grimmett, Equation (1.12), reduced to the coded straight-path Peierls geometry package. -/
theorem cubicCriticalProbability_two_bounds_of_planarPeierlsCodedStraightGeometry
    (G : PlanarPeierlsCodedStraightGeometry) :
    1 / cubicConnectiveConstant 2 ≤ cubicCriticalProbability 2 ∧
      cubicCriticalProbability 2 ≤ 1 - 1 / cubicConnectiveConstant 2 :=
  cubicCriticalProbability_two_bounds_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs

/-- Grimmett, Theorem (1.10), reduced to the coded straight-path Peierls geometry package. -/
theorem cubicCriticalProbability_pos_lt_one_of_planarPeierlsCodedStraightGeometry
    (G : PlanarPeierlsCodedStraightGeometry) {d : ℕ} (hd : 2 ≤ d) :
    0 < cubicCriticalProbability d ∧ cubicCriticalProbability d < 1 :=
  cubicCriticalProbability_pos_lt_one_of_grimmettTheorem110Inputs G.toGrimmettTheorem110Inputs hd

end Percolation
