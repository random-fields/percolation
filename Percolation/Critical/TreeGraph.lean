import Percolation.Critical.TwoPoint
import Percolation.Bernoulli.DisjointConnections
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Tree-graph inequalities and cluster moments

This file formalizes the graph-theoretic and probabilistic core of Grimmett's Section 6.3.
The first result is the corrected finite-terminal formulation of Lemma 6.87.  The ambient graph
may be infinite; only the terminal family is finite.
-/

namespace Percolation

open Set SimpleGraph
open scoped unitInterval ENNReal BigOperators

variable {V : Type*} (G : SimpleGraph V)

/-- Deleting a vertex after first restricting to a finite induced subgraph is canonically the
same as inducing on the erased finite vertex set. -/
private def induceComplSingletonIsoErase [DecidableEq V] (S : Finset V) (v : S) :
    (G.induce (S : Set V)).induce ({v}ᶜ : Set S) ≃g
      G.induce (↑(S.erase v) : Set V) where
  toEquiv :=
    { toFun := fun x ↦ ⟨x.1.1, by
        have hxS : x.1.1 ∈ S := x.1.2
        have hxv : x.1 ≠ v := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
        simp only [Finset.mem_coe, Finset.mem_erase]
        exact ⟨fun h ↦ hxv (Subtype.ext h), hxS⟩⟩
      invFun := fun x ↦ ⟨⟨x.1, (Finset.mem_erase.mp x.2).2⟩, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)⟩
      left_inv := fun x ↦ by cases x; rfl
      right_inv := fun x ↦ by cases x; rfl }
  map_rel_iff' := by
    intro x y
    rfl

/-- Forget the finite induced carrier after deleting all edges incident to `v`. -/
private def induceEraseToDeleteHom [DecidableEq V] (S : Finset V) (v : S) :
    G.induce (↑(S.erase (v : V)) : Set V) →g G.deleteIncidenceSet (v : V) where
  toFun z := z.1
  map_rel' := by
    intro a b hab
    rw [SimpleGraph.deleteIncidenceSet_adj]
    exact ⟨hab, (Finset.mem_erase.mp a.2).1,
      (Finset.mem_erase.mp b.2).1⟩

/-- The identity homomorphism from the graph with one incidence set deleted. -/
private def deleteIncidenceHom (v : V) : G.deleteIncidenceSet v →g G where
  toFun := id
  map_rel' := fun h ↦ G.deleteIncidenceSet_le v h

/-- A finite nonempty terminal set in a connected graph contains a terminal whose deletion leaves
all remaining terminals in one connected component.  This is Grimmett, Lemma 6.87, with the
finiteness condition made explicit; the ambient graph itself need not be finite. -/
theorem exists_terminal_deletion_preserves_connected
    (hG : G.Connected) (W : Finset V) (hW : W.Nonempty) :
    ∃ w ∈ W, ∀ x, x ∈ W → x ≠ w → ∀ y, y ∈ W → y ≠ w →
      (G.deleteIncidenceSet w).Reachable x y := by
  classical
  have hext := SimpleGraph.extend_finset_to_connected hG.preconnected hW
  have hexists : ∃ n : ℕ, ∃ S : Finset V,
      W ⊆ S ∧ (G.induce (S : Set V)).Connected ∧ S.card = n := by
    obtain ⟨S, hWS, hS⟩ := hext
    exact ⟨S.card, S, hWS, hS, rfl⟩
  let n := Nat.find hexists
  obtain ⟨S, hWS, hSconn, hScard⟩ := Nat.find_spec hexists
  let H : SimpleGraph S := G.induce (S : Set V)
  have hHconn : H.Connected := hSconn
  obtain ⟨v, hvpre⟩ :=
    hHconn.exists_preconnected_induce_compl_singleton_of_finite
  have hvW : (v : V) ∈ W := by
    by_contra hvW
    let S' := S.erase (v : V)
    have hWS' : W ⊆ S' := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun hxv ↦ hvW (hxv ▸ hx), hWS hx⟩
    have hS'nonempty : (↑S' : Set V).Nonempty := by
      obtain ⟨x, hx⟩ := hW
      exact ⟨x, hWS' hx⟩
    let e := induceComplSingletonIsoErase G S v
    haveI : Nonempty {x : S // x ∈ ({v}ᶜ : Set S)} := by
      obtain ⟨x, hx⟩ := hS'nonempty
      exact ⟨e.symm ⟨x, hx⟩⟩
    have hsrc : (H.induce ({v}ᶜ : Set S)).Connected := ⟨hvpre⟩
    have hS'conn : (G.induce (↑S' : Set V)).Connected :=
      e.connected_iff.mp hsrc
    have hsmaller : S'.card < n := by
      change S'.card < Nat.find hexists
      rw [← hScard]
      exact Finset.card_erase_lt_of_mem v.2
    have hmin := Nat.find_min' hexists
      ⟨S', hWS', hS'conn, rfl⟩
    exact (not_lt_of_ge hmin) hsmaller
  refine ⟨v, hvW, ?_⟩
  intro x hx hxv y hy hyv
  let e := induceComplSingletonIsoErase G S v
  have hxS : x ∈ S := hWS hx
  have hyS : y ∈ S := hWS hy
  let xs : {z : S // z ∈ ({v}ᶜ : Set S)} :=
    ⟨⟨x, hxS⟩, by simpa using fun h : (⟨x, hxS⟩ : S) = v ↦ hxv (congrArg Subtype.val h)⟩
  let ys : {z : S // z ∈ ({v}ᶜ : Set S)} :=
    ⟨⟨y, hyS⟩, by simpa using fun h : (⟨y, hyS⟩ : S) = v ↦ hyv (congrArg Subtype.val h)⟩
  have hxy : (H.induce ({v}ᶜ : Set S)).Reachable xs ys := hvpre xs ys
  have hxyErase : (G.induce (↑(S.erase (v : V)) : Set V)).Reachable (e xs) (e ys) :=
    hxy.map e.toHom
  let f := induceEraseToDeleteHom G S v
  have hmapped := hxyErase.map f
  simpa [e, induceComplSingletonIsoErase, xs, ys] using hmapped

/-! ### The three-terminal tripod -/

/-- Split two paths at the first point where the second path meets the first.  The three resulting
branches have pairwise disjoint edge lists. -/
private theorem exists_firstHit_tripod [DecidableEq V]
    {a b c : V} {p : G.Walk a b} {q : G.Walk c a}
    (hp : p.IsPath) :
    ∃ u : V, ∃ wa : G.Walk u a, ∃ wb : G.Walk u b, ∃ wc : G.Walk u c,
      wa.edges.Disjoint wb.edges ∧ wa.edges.Disjoint wc.edges ∧
        wb.edges.Disjoint wc.edges := by
  classical
  have hex : ∃ j : ℕ, j ≤ q.length ∧ q.getVert j ∈ p.support := by
    refine ⟨q.length, le_rfl, ?_⟩
    simpa using p.start_mem_support
  let j := Nat.find hex
  have hj : j ≤ q.length ∧ q.getVert j ∈ p.support := Nat.find_spec hex
  let u := q.getVert j
  have huP : u ∈ p.support := hj.2
  let r : G.Walk c u := q.take j
  let wa : G.Walk u a := (p.takeUntil u huP).reverse
  let wb : G.Walk u b := p.dropUntil u huP
  let wc : G.Walk u c := r.reverse
  have hrP : r.edges.Disjoint p.edges := by
    rw [List.disjoint_left]
    intro e her hepEdge
    induction e using Sym2.inductionOn with
    | _ z t =>
      have hzt : z ≠ t := (r.adj_of_mem_edges her).ne
      let s : V := if z = u then t else z
      have hsne : s ≠ u := by
        dsimp [s]
        split_ifs with hzu
        · intro htu
          exact hzt (hzu.trans htu.symm)
        · exact ‹z ≠ u›
      have hsR : s ∈ r.support := by
        dsimp [s]
        split_ifs
        · exact r.snd_mem_support_of_mem_edges her
        · exact r.fst_mem_support_of_mem_edges her
      have hsP : s ∈ p.support := by
        dsimp [s]
        split_ifs
        · exact p.snd_mem_support_of_mem_edges hepEdge
        · exact p.fst_mem_support_of_mem_edges hepEdge
      obtain ⟨i, hiEq, hiLen⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hsR
      have hrlen : r.length = j := by
        dsimp [r]
        rw [q.take_length, min_eq_left hj.1]
      have hiJ : i ≤ j := by simpa [hrlen] using hiLen
      have hqi : q.getVert i = s := by
        have := congrArg id hiEq
        simpa [r, q.take_getVert, min_eq_right hiJ] using hiEq
      have hij : i < j := by
        apply lt_of_le_of_ne hiJ
        intro hijEq
        apply hsne
        rw [← hiEq, hijEq]
        simp [r, u, q.take_getVert]
      have hcandidate : i ≤ q.length ∧ q.getVert i ∈ p.support :=
        ⟨hiJ.trans hj.1, hqi.symm ▸ hsP⟩
      exact (not_lt_of_ge (Nat.find_min' hex hcandidate)) hij
  have hab : wa.edges.Disjoint wb.edges := by
    have hsplit := hp.isTrail.disjoint_edges_takeUntil_dropUntil huP
    simpa [wa, wb, List.disjoint_reverse_left] using hsplit
  have hac : wa.edges.Disjoint wc.edges := by
    have hsub : wa.edges ⊆ p.edges := by
      intro e he
      have he' : e ∈ (p.takeUntil u huP).edges := by simpa [wa] using he
      exact p.edges_takeUntil_subset huP he'
    rw [List.disjoint_left]
    intro e hewa hewc
    have hep := hsub hewa
    have her : e ∈ r.edges := by simpa [wc] using hewc
    exact hrP her hep
  have hbc : wb.edges.Disjoint wc.edges := by
    have hsub : wb.edges ⊆ p.edges := p.edges_dropUntil_subset huP
    rw [List.disjoint_left]
    intro e hewb hewc
    have hep := hsub hewb
    have her : e ∈ r.edges := by simpa [wc] using hewc
    exact hrP her hep
  exact ⟨u, wa, wb, wc, hab, hac, hbc⟩

/-- A connected graph together with a path between `a,b` after deleting `c` contains an
edge-disjoint tripod to `a,b,c`. -/
private theorem exists_tripod_of_deleted_terminal [DecidableEq V]
    (hG : G.Connected) {a b c : V}
    (hdel : (G.deleteIncidenceSet c).Reachable a b) :
    ∃ u : V, ∃ wa : G.Walk u a, ∃ wb : G.Walk u b, ∃ wc : G.Walk u c,
      wa.edges.Disjoint wb.edges ∧ wa.edges.Disjoint wc.edges ∧
        wb.edges.Disjoint wc.edges := by
  obtain ⟨pdel, hpdel⟩ := hdel.exists_isPath
  let p : G.Walk a b := pdel.mapLe (G.deleteIncidenceSet_le c)
  have hp : p.IsPath := hpdel.mapLe (G.deleteIncidenceSet_le c)
  obtain ⟨q, hq⟩ := hG.exists_isPath c a
  exact exists_firstHit_tripod G (p := p) (q := q) hp

/-- Every three vertices of a connected graph admit a common centre and three pairwise
edge-disjoint paths to the terminals.  Zero-length paths handle repeated terminals exactly. -/
theorem exists_three_pairwise_edgeDisjoint_walks [DecidableEq V]
    (hG : G.Connected) (x₀ x₁ x₂ : V) :
    ∃ u : V, ∃ w₀ : G.Walk u x₀, ∃ w₁ : G.Walk u x₁, ∃ w₂ : G.Walk u x₂,
      w₀.edges.Disjoint w₁.edges ∧ w₀.edges.Disjoint w₂.edges ∧
        w₁.edges.Disjoint w₂.edges := by
  by_cases h01 : x₀ = x₁
  · subst x₁
    obtain ⟨w₂, _hw₂⟩ := hG.exists_isPath x₀ x₂
    exact ⟨x₀, .nil, .nil, w₂, by simp⟩
  by_cases h02 : x₀ = x₂
  · subst x₂
    obtain ⟨w₁, _hw₁⟩ := hG.exists_isPath x₀ x₁
    exact ⟨x₀, .nil, w₁, .nil, by simp⟩
  by_cases h12 : x₁ = x₂
  · subst x₂
    obtain ⟨w₀, _hw₀⟩ := hG.exists_isPath x₁ x₀
    exact ⟨x₁, w₀, .nil, .nil, by simp⟩
  let W : Finset V := {x₀, x₁, x₂}
  have hW : W.Nonempty := ⟨x₀, by simp [W]⟩
  obtain ⟨c, hcW, hdelete⟩ :=
    exists_terminal_deletion_preserves_connected G hG W hW
  simp only [W, Finset.mem_insert, Finset.mem_singleton] at hcW
  rcases hcW with hc0 | hc1 | hc2
  · subst c
    have hdel : (G.deleteIncidenceSet x₀).Reachable x₁ x₂ :=
      hdelete x₁ (by simp [W]) (fun h ↦ h01 h.symm)
        x₂ (by simp [W]) (fun h ↦ h02 h.symm)
    obtain ⟨u, w₁, w₂, w₀, h12', h10, h20⟩ :=
      exists_tripod_of_deleted_terminal G hG hdel
    exact ⟨u, w₀, w₁, w₂, h10.symm, h20.symm, h12'⟩
  · subst c
    have hdel : (G.deleteIncidenceSet x₁).Reachable x₀ x₂ :=
      hdelete x₀ (by simp [W]) h01 x₂ (by simp [W]) (fun h ↦ h12 h.symm)
    obtain ⟨u, w₀, w₂, w₁, h02', h01', h21⟩ :=
      exists_tripod_of_deleted_terminal G hG hdel
    exact ⟨u, w₀, w₁, w₂, h01', h02', h21.symm⟩
  · subst c
    have hdel : (G.deleteIncidenceSet x₂).Reachable x₀ x₁ :=
      hdelete x₀ (by simp [W]) h02 x₁ (by simp [W]) h12
    obtain ⟨u, w₀, w₁, w₂, h01', h02', h12'⟩ :=
      exists_tripod_of_deleted_terminal G hG hdel
    exact ⟨u, w₀, w₁, w₂, h01', h02', h12'⟩

/-- Component-local version of the tripod theorem: global connectedness is unnecessary when the
three specified terminals are already mutually reachable. -/
theorem exists_three_pairwise_edgeDisjoint_walks_of_reachable [DecidableEq V]
    {x₀ x₁ x₂ : V} (h01 : G.Reachable x₀ x₁) (h02 : G.Reachable x₀ x₂) :
    ∃ u : V, ∃ w₀ : G.Walk u x₀, ∃ w₁ : G.Walk u x₁, ∃ w₂ : G.Walk u x₂,
      w₀.edges.Disjoint w₁.edges ∧ w₀.edges.Disjoint w₂.edges ∧
        w₁.edges.Disjoint w₂.edges := by
  let C := G.connectedComponentMk x₀
  have hx₀ : x₀ ∈ C := by rfl
  have hx₁ : x₁ ∈ C := by
    change G.connectedComponentMk x₁ = G.connectedComponentMk x₀
    exact (SimpleGraph.ConnectedComponent.sound h01).symm
  have hx₂ : x₂ ∈ C := by
    change G.connectedComponentMk x₂ = G.connectedComponentMk x₀
    exact (SimpleGraph.ConnectedComponent.sound h02).symm
  obtain ⟨u, w₀, w₁, w₂, h01', h02', h12'⟩ :=
    exists_three_pairwise_edgeDisjoint_walks C.toSimpleGraph
      C.connected_toSimpleGraph ⟨x₀, hx₀⟩ ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  let f := C.toSimpleGraph_hom
  let q₀ : G.Walk u.1 x₀ := (w₀.map f).copy rfl rfl
  let q₁ : G.Walk u.1 x₁ := (w₁.map f).copy rfl rfl
  let q₂ : G.Walk u.1 x₂ := (w₂.map f).copy rfl rfl
  have hmapInj : Function.Injective (Sym2.map ((↑) : C → V)) :=
    Sym2.map.injective Subtype.val_injective
  have hq01 : q₀.edges.Disjoint q₁.edges := by
    simpa [q₀, q₁, f, SimpleGraph.Walk.edges_map] using h01'.map hmapInj
  have hq02 : q₀.edges.Disjoint q₂.edges := by
    simpa [q₀, q₂, f, SimpleGraph.Walk.edges_map] using h02'.map hmapInj
  have hq12 : q₁.edges.Disjoint q₂.edges := by
    simpa [q₁, q₂, f, SimpleGraph.Walk.edges_map] using h12'.map hmapInj
  exact ⟨u.1, q₀, q₁, q₂, hq01, hq02, hq12⟩

/-! ### Lemma 6.89 -/

/-- The endpoint-safe `ℝ≥0∞` form of the two-point connectivity. -/
noncomputable def twoPointConnectivityENNReal
    (d : ℕ) (p : I) (x y : Cubic d) : ℝ≥0∞ :=
  bernoulliBondMeasure d p (connectionEvent d x y)

theorem twoPointConnectivityENNReal_eq_ofReal
    (d : ℕ) (p : I) (x y : Cubic d) :
    twoPointConnectivityENNReal d p x y = ENNReal.ofReal (twoPointConnectivity d p x y) := by
  rw [twoPointConnectivityENNReal, twoPointConnectivity, MeasureTheory.ofReal_measureReal]

/-- The event that three terminals belong to the same open cluster. -/
def threePointConnectionEvent (d : ℕ) (x₀ x₁ x₂ : Cubic d) : Set (EdgeConfiguration d) :=
  connectionEvent d x₀ x₁ ∩ connectionEvent d x₀ x₂

/-- The disjoint tripod event with a prescribed centre. -/
inductive TripodIndex
  | zero | one | two
  deriving DecidableEq, Fintype

def tripodTerminal {d : ℕ} (x₀ x₁ x₂ : Cubic d) : TripodIndex → Cubic d
  | .zero => x₀
  | .one => x₁
  | .two => x₂

def tripodDisjointConnectionEvent (d : ℕ) (u x₀ x₁ x₂ : Cubic d) :
    Set (EdgeConfiguration d) :=
  ExistsPairwiseDisjointOpenWalks d (Finset.univ : Finset TripodIndex)
    (fun _ ↦ u) (tripodTerminal x₀ x₁ x₂)

private theorem disjoint_walkEdgeFinset_of_edges_disjoint
    {d : ℕ} {a b c : Cubic d} {p : (cubicGraph d).Walk a b}
    {q : (cubicGraph d).Walk a c} (h : p.edges.Disjoint q.edges) :
    Disjoint (walkEdgeFinset p) (walkEdgeFinset q) := by
  rw [Finset.disjoint_left]
  intro e hep heq
  rw [mem_walkEdgeFinset_iff] at hep heq
  exact h hep heq

/-- Deterministic content of (6.88): a three-point connection contains a disjoint tripod. -/
theorem threePointConnectionEvent_subset_iUnion_tripod
    (d : ℕ) (x₀ x₁ x₂ : Cubic d) :
    threePointConnectionEvent d x₀ x₁ x₂ ⊆
      ⋃ u : Cubic d, tripodDisjointConnectionEvent d u x₀ x₁ x₂ := by
  classical
  rintro ω ⟨⟨p01, hp01⟩, ⟨p02, hp02⟩⟩
  let Gω := cubicOpenGraph d ω
  let q01 : Gω.Walk x₀ x₁ :=
    (nonempty_cubicOpenGraph_walk_of_walkIsOpen p01 hp01).some
  let q02 : Gω.Walk x₀ x₂ :=
    (nonempty_cubicOpenGraph_walk_of_walkIsOpen p02 hp02).some
  obtain ⟨u, w₀, w₁, w₂, h01, h02, h12⟩ :=
    exists_three_pairwise_edgeDisjoint_walks_of_reachable Gω
      q01.reachable q02.reachable
  let r₀ : (cubicGraph d).Walk u x₀ := w₀.map (cubicOpenGraphHom d ω)
  let r₁ : (cubicGraph d).Walk u x₁ := w₁.map (cubicOpenGraphHom d ω)
  let r₂ : (cubicGraph d).Walk u x₂ := w₂.map (cubicOpenGraphHom d ω)
  have hopenInj : Function.Injective (cubicOpenGraphHom d ω) := by
    intro a b h
    exact h
  have hr01 : r₀.edges.Disjoint r₁.edges := by
    change (w₀.map (cubicOpenGraphHom d ω)).edges.Disjoint
      (w₁.map (cubicOpenGraphHom d ω)).edges
    rw [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map]
    exact h01.map (Sym2.map.injective hopenInj)
  have hr02 : r₀.edges.Disjoint r₂.edges := by
    change (w₀.map (cubicOpenGraphHom d ω)).edges.Disjoint
      (w₂.map (cubicOpenGraphHom d ω)).edges
    rw [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map]
    exact h02.map (Sym2.map.injective hopenInj)
  have hr12 : r₁.edges.Disjoint r₂.edges := by
    change (w₁.map (cubicOpenGraphHom d ω)).edges.Disjoint
      (w₂.map (cubicOpenGraphHom d ω)).edges
    rw [SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map]
    exact h12.map (Sym2.map.injective hopenInj)
  rw [Set.mem_iUnion]
  refine ⟨u, ?_⟩
  let w : ∀ i : TripodIndex,
      (cubicGraph d).Walk u (tripodTerminal x₀ x₁ x₂ i)
    | .zero => r₀
    | .one => r₁
    | .two => r₂
  refine ⟨w, ?_, ?_⟩
  · intro i _hi
    cases i with
    | zero => exact walkIsOpen_map_cubicOpenGraphHom w₀
    | one => exact walkIsOpen_map_cubicOpenGraphHom w₁
    | two => exact walkIsOpen_map_cubicOpenGraphHom w₂
  · intro i _hi j _hj hij
    cases i <;> cases j <;> simp_all [w]
    · exact disjoint_walkEdgeFinset_of_edges_disjoint hr01
    · exact disjoint_walkEdgeFinset_of_edges_disjoint hr02
    · exact (disjoint_walkEdgeFinset_of_edges_disjoint hr01).symm
    · exact disjoint_walkEdgeFinset_of_edges_disjoint hr12
    · exact (disjoint_walkEdgeFinset_of_edges_disjoint hr02).symm
    · exact (disjoint_walkEdgeFinset_of_edges_disjoint hr12).symm

/-- Grimmett, Lemma 6.89, in endpoint-safe `ℝ≥0∞` form.  This codomain is essential at densities
where the infinite sum is not summable as a real series. -/
theorem threePointConnectivity_le_tsum_prod
    (d : ℕ) (p : I) (x₀ x₁ x₂ : Cubic d) :
    bernoulliBondMeasure d p (threePointConnectionEvent d x₀ x₁ x₂) ≤
      ∑' u : Cubic d,
        twoPointConnectivityENNReal d p u x₀ *
          twoPointConnectivityENNReal d p u x₁ *
            twoPointConnectivityENNReal d p u x₂ := by
  let μ := bernoulliBondMeasure d p
  let D := fun u : Cubic d ↦ tripodDisjointConnectionEvent d u x₀ x₁ x₂
  calc
    μ (threePointConnectionEvent d x₀ x₁ x₂) ≤ μ (⋃ u, D u) :=
      MeasureTheory.measure_mono (threePointConnectionEvent_subset_iUnion_tripod d x₀ x₁ x₂)
    _ ≤ ∑' u, μ (D u) := MeasureTheory.measure_iUnion_le _
    _ ≤ ∑' u : Cubic d,
        twoPointConnectivityENNReal d p u x₀ *
          twoPointConnectivityENNReal d p u x₁ *
            twoPointConnectivityENNReal d p u x₂ := by
      apply ENNReal.tsum_le_tsum
      intro u
      rw [← MeasureTheory.ofReal_measureReal (μ := μ) (s := D u)]
      have hbk := bernoulliBondMeasure_real_existsPairwiseDisjointOpenWalks_le_prod
        d p (Finset.univ : Finset TripodIndex) (fun _ ↦ u)
          (tripodTerminal x₀ x₁ x₂)
      have huniv : (Finset.univ : Finset TripodIndex) =
          {TripodIndex.zero, TripodIndex.one, TripodIndex.two} := by decide
      calc
        ENNReal.ofReal (μ.real (D u)) ≤
            ENNReal.ofReal (twoPointConnectivity d p u x₀ *
              twoPointConnectivity d p u x₁ * twoPointConnectivity d p u x₂) := by
          apply ENNReal.ofReal_le_ofReal
          rw [huniv] at hbk
          simpa [μ, D, tripodDisjointConnectionEvent, tripodTerminal,
            twoPointConnectivity, mul_assoc] using hbk
        _ = twoPointConnectivityENNReal d p u x₀ *
              twoPointConnectivityENNReal d p u x₁ *
                twoPointConnectivityENNReal d p u x₂ := by
          rw [twoPointConnectivityENNReal_eq_ofReal,
            twoPointConnectivityENNReal_eq_ofReal,
            twoPointConnectivityENNReal_eq_ofReal,
            ENNReal.ofReal_mul (mul_nonneg (twoPointConnectivity_nonneg d p u x₀)
              (twoPointConnectivity_nonneg d p u x₁)),
            ENNReal.ofReal_mul (twoPointConnectivity_nonneg d p u x₀)]

/-! ### Labelled skeleton enumeration (6.95)--(6.96) -/

/-- Number of isomorphism classes of labelled trivalent skeletons with `n` exterior vertices.
The source only uses `n ≥ 3`; totalized values below three are harmless implementation detail. -/
def connectivitySkeletonCount (n : ℕ) : ℕ := Nat.doubleFactorial (2 * n - 5)

/-- Finite cardinality-facing index for labelled skeletons. -/
abbrev CubicConnectivitySkeletonIndex (n : ℕ) := Fin (connectivitySkeletonCount n)

@[simp] theorem connectivitySkeletonCount_three : connectivitySkeletonCount 3 = 1 := by decide
@[simp] theorem connectivitySkeletonCount_four : connectivitySkeletonCount 4 = 3 := by decide
@[simp] theorem connectivitySkeletonCount_five : connectivitySkeletonCount 5 = 15 := by decide

/-- Recurrence (6.95): insert the newest exterior vertex into one of the `2n-3` old edges. -/
theorem connectivitySkeletonCount_succ {n : ℕ} (hn : 3 ≤ n) :
    connectivitySkeletonCount (n + 1) = (2 * n - 3) * connectivitySkeletonCount n := by
  unfold connectivitySkeletonCount
  have h₁ : 2 * (n + 1) - 5 = (2 * n - 5) + 2 := by omega
  have h₂ : 2 * n - 5 + 2 = 2 * n - 3 := by omega
  rw [h₁, Nat.doubleFactorial_add_two, h₂]

/-- Factorial form of (6.96).  Multiplication is used instead of truncated natural-number
division, so the statement records the exact arithmetic identity without a divisibility side
condition hidden in notation. -/
theorem connectivitySkeletonCount_eq_doubleFactorial
    {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (n - 1) * Nat.factorial (n - 1) * connectivitySkeletonCount (n + 1) =
      Nat.factorial (2 * n - 2) := by
  have hEven : 2 * n - 2 = 2 * (n - 1) := by omega
  have hOdd : 2 * (n + 1) - 5 = 2 * n - 3 := by omega
  have hSucc : 2 * n - 2 = (2 * n - 3) + 1 := by omega
  rw [← Nat.doubleFactorial_two_mul (n - 1), connectivitySkeletonCount, hOdd]
  rw [← hEven, hSucc]
  exact (Nat.factorial_eq_mul_doubleFactorial (2 * n - 3)).symm

#print axioms exists_terminal_deletion_preserves_connected
#print axioms threePointConnectivity_le_tsum_prod
#print axioms connectivitySkeletonCount_eq_doubleFactorial

end Percolation
