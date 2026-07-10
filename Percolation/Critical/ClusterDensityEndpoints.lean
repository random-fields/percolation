import Percolation.Critical.ConcreteClusterSeries
import Percolation.Critical.AppendixLimits
import Percolation.Critical.TorusGhostJoint
import Percolation.Bernoulli.Russo

/-!
# Endpoint estimates for the open-cluster density

This file completes the endpoint part of Grimmett's Theorem 4.31.  The small-density endpoint
uses the concrete animal expansion.  At the high-density endpoint we use periodic finite-volume
component counts: a square detour shows that a closed bond can merge two components only if one
of three other bonds is closed.  Appendix I then passes this uniform estimate to the infinite
lattice.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal unitInterval Topology

noncomputable section

private theorem finset_insert_classical_eq {α : Type*} [DecidableEq α] (a : α) (s : Finset α) :
    @insert α (Finset α) (@Finset.instInsert α (Classical.decEq α)) a s = insert a s := by
  ext x
  simp

private theorem finset_erase_classical_eq {α : Type*} [DecidableEq α] (s : Finset α) (a : α) :
    @Finset.erase α (Classical.decEq α) s a = s.erase a := by
  ext x
  simp

theorem reachable_sup_edge_iff {V : Type*} (G : SimpleGraph V) {u v x y : V}
    (huv : u ≠ v) :
    (G ⊔ SimpleGraph.edge u v).Reachable x y ↔
      G.Reachable x y ∨
        (G.Reachable x u ∧ G.Reachable v y) ∨
        (G.Reachable x v ∧ G.Reachable u y) := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Or.inl .rfl
    | @cons a b c hab q ih =>
        rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hab
        rcases hab with hab | ⟨hab, _hne⟩
        · have habr : G.Reachable a b := hab.reachable
          rcases ih with hbc | hbc | hbc
          · exact Or.inl (habr.trans hbc)
          · exact Or.inr (Or.inl ⟨habr.trans hbc.1, hbc.2⟩)
          · exact Or.inr (Or.inr ⟨habr.trans hbc.1, hbc.2⟩)
        · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases ih with h | h | h
            · exact Or.inr (Or.inl ⟨.rfl, h⟩)
            · exact Or.inl (h.1.symm.trans h.2)
            · exact Or.inl h.2
          · rcases ih with h | h | h
            · exact Or.inr (Or.inr ⟨.rfl, h⟩)
            · exact Or.inl h.2
            · exact Or.inl (h.1.symm.trans h.2)
  · intro h
    have hle : G ≤ G ⊔ SimpleGraph.edge u v := le_sup_left
    have huvAdj : (G ⊔ SimpleGraph.edge u v).Adj u v := by
      rw [SimpleGraph.sup_adj]
      exact Or.inr ((SimpleGraph.edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩)
    rcases h with h | h | h
    · exact h.mono hle
    · exact ((h.1.mono hle).trans huvAdj.reachable).trans (h.2.mono hle)
    · exact ((h.1.mono hle).trans huvAdj.symm.reachable).trans (h.2.mono hle)

theorem connectedComponent_card_le_add_one_sup_edge
    {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V} (huv : u ≠ v) :
    Nat.card G.ConnectedComponent ≤
      Nat.card (G ⊔ SimpleGraph.edge u v).ConnectedComponent + 1 := by
  classical
  let H := G ⊔ SimpleGraph.edge u v
  let φ : G.ConnectedComponent → H.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE le_sup_left)
  let cv := G.connectedComponentMk v
  let A := {c : G.ConnectedComponent // c ≠ cv}
  let f : A → H.ConnectedComponent := fun c ↦ φ c
  have hf : Function.Injective f := by
    intro c d hcd
    rcases c.1.exists_rep with ⟨x, hx⟩
    rcases d.1.exists_rep with ⟨y, hy⟩
    apply Subtype.ext
    rw [← hx, ← hy]
    dsimp only [f, φ] at hcd
    rw [← hx, ← hy] at hcd
    change H.connectedComponentMk x = H.connectedComponentMk y at hcd
    have hH : H.Reachable x y := SimpleGraph.ConnectedComponent.eq.mp hcd
    rcases (reachable_sup_edge_iff G huv).mp hH with hxy | hxy | hxy
    · exact SimpleGraph.ConnectedComponent.eq.mpr hxy
    · exfalso
      apply d.2
      dsimp only [cv]
      rw [← hy]
      exact SimpleGraph.ConnectedComponent.eq.mpr hxy.2.symm
    · exfalso
      apply c.2
      dsimp only [cv]
      rw [← hx]
      exact SimpleGraph.ConnectedComponent.eq.mpr hxy.1
  have hcardA : Fintype.card A ≤ Fintype.card H.ConnectedComponent :=
    Fintype.card_le_of_injective f hf
  have hcardAeq : Fintype.card A = Fintype.card G.ConnectedComponent - 1 := by
    dsimp only [A]
    rw [Fintype.card_subtype_compl (fun c : G.ConnectedComponent ↦ c = cv)]
    simp
  rw [hcardAeq] at hcardA
  simpa [Nat.card_eq_fintype_card, H] using (show
    Fintype.card G.ConnectedComponent - 1 ≤ Fintype.card H.ConnectedComponent from hcardA)

theorem connectedComponent_card_sup_edge_eq_of_reachable
    {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (huvReach : G.Reachable u v) :
    Nat.card (G ⊔ SimpleGraph.edge u v).ConnectedComponent =
      Nat.card G.ConnectedComponent := by
  let H := G ⊔ SimpleGraph.edge u v
  let φ : G.ConnectedComponent → H.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE le_sup_left)
  have hφsurj : Function.Surjective φ :=
    SimpleGraph.ConnectedComponent.surjective_map_ofLE le_sup_left
  have hφinj : Function.Injective φ := by
    intro c d hcd
    rcases c.exists_rep with ⟨x, hx⟩
    rcases d.exists_rep with ⟨y, hy⟩
    rw [← hx, ← hy]
    dsimp only [φ] at hcd
    rw [← hx, ← hy] at hcd
    change H.connectedComponentMk x = H.connectedComponentMk y at hcd
    have hH : H.Reachable x y := SimpleGraph.ConnectedComponent.eq.mp hcd
    rcases (reachable_sup_edge_iff G huv).mp hH with hxy | hxy | hxy
    · exact SimpleGraph.ConnectedComponent.eq.mpr hxy
    · exact SimpleGraph.ConnectedComponent.eq.mpr
        ((hxy.1.trans huvReach).trans hxy.2)
    · exact SimpleGraph.ConnectedComponent.eq.mpr
        ((hxy.1.trans huvReach.symm).trans hxy.2)
  exact Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm

/-- The expected reciprocal size of the origin cluster on the periodic lattice, written as its
finite cluster-size series.  By transitivity this is also the expected number of periodic open
components per vertex. -/
def torusClusterDensitySeries (d N : ℕ) (hN : 2 ≤ N) (p : I) : ℝ :=
  ∑' n : ℕ, (1 / (n : ℝ)) * torusFiniteClusterSizeProbability d N hN p n

private theorem torusClusterDensitySeries_tendsto_openClustersPerVertex_aux
    (d : ℕ) (p : I) :
    Tendsto (fun j : ℕ ↦ torusClusterDensitySeries d (j + 2) (by omega) p)
      atTop (nhds (openClustersPerVertex d p)) := by
  let a : ℕ → ℕ → ℝ := fun j n ↦
    torusFiniteClusterSizeProbability d (j + 2) (by omega) p n
  let b : ℕ → ℝ := finiteClusterSizeProbability d p
  let w : ℕ → ℝ := fun n ↦ 1 / (n : ℝ)
  have hlimit := tendsto_tsum_of_stabilizes_dominated_by_probability
    a b (fun j n ↦ w n * a j n) (fun n ↦ w n * b n) w
    (C := 1)
    (fun j n ↦ by
      dsimp only [a]
      unfold torusFiniteClusterSizeProbability
      exact measureReal_nonneg)
    (finiteClusterSizeProbability_nonneg d p)
    (fun j ↦ summable_torusFiniteClusterSizeProbability d (j + 2) (by omega) p)
    (summable_finiteClusterSizeProbability d p)
    (fun j ↦ by rw [tsum_torusFiniteClusterSizeProbability_eq_one])
    (by rw [tsum_finiteClusterSizeProbability_eq_one_sub_theta]; exact sub_le_self _ measureReal_nonneg)
    (by
      intro n j hnj
      dsimp only [a, b, w]
      rw [torusFiniteClusterSizeProbability_eq_finiteClusterSizeProbability
        (d := d) (N := j + 2) (n := n) (by omega) (by omega) p])
    (fun n ↦ one_div_nonneg.mpr (Nat.cast_nonneg n))
    (fun n ↦ by
      by_cases hn : n = 0
      · simp [w, hn]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        simpa [w] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1)
    (fun j n ↦ by
      dsimp only [a, w]
      rw [abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n))
        (by unfold torusFiniteClusterSizeProbability; exact measureReal_nonneg))])
    (fun n ↦ by
      dsimp only [b, w]
      rw [abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n))
        (finiteClusterSizeProbability_nonneg d p n))])
    (by simpa [w] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simpa only [torusClusterDensitySeries, a, b, w,
    openClustersPerVertex_eq_tsum_finiteClusterSizeProbability] using hlimit

theorem finiteBernoulliExpectation_map_equiv
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (p : ℝ) (f : ι ≃ ι)
    (hE : E.map f.toEmbedding = E) (X : Finset ι → ℝ) :
    finiteBernoulliExpectation E p (fun s ↦ X (s.map f.toEmbedding)) =
      finiteBernoulliExpectation E p X := by
  unfold finiteBernoulliExpectation
  refine Finset.sum_nbij' (fun s ↦ s.map f.toEmbedding)
    (fun s ↦ s.map f.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powerset] at hs ⊢
    rw [← hE]
    exact Finset.map_subset_map.mpr hs
  · intro s hs
    rw [Finset.mem_powerset] at hs ⊢
    have hEinv : E.map f.symm.toEmbedding = E := by
      ext x
      have hx := congrArg (fun S : Finset ι ↦ f x ∈ S) hE
      simpa using hx.symm
    rw [← hEinv]
    exact Finset.map_subset_map.mpr hs
  · intro s _hs
    ext x
    simp
  · intro s _hs
    ext x
    simp
  · intro s _hs
    have hsE : s ⊆ E := Finset.mem_powerset.mp _hs
    have hmapE : s.map f.toEmbedding ⊆ E := by
      rw [← hE]
      exact Finset.map_subset_map.mpr hsE
    rw [← finiteBernoulliWeightFamily_const hsE p,
      ← finiteBernoulliWeightFamily_const hmapE p,
      finiteBernoulliWeightFamily_map_equiv E (fun _ ↦ p) f hE (fun _ ↦ rfl) s]

/-- The finite periodic open cluster from an arbitrary root. -/
def cubicTorusOpenClusterFromFinset (d N : ℕ) (hN : 2 ≤ N)
    (ω : CubicTorusEdgeConfiguration d N) (x : CubicTorus d N) :
    Finset (CubicTorus d N) :=
  restrictTo (cubicTorusVertexFinset d N hN) (cubicTorusOpenClusterFrom d N ω x)

@[simp]
theorem mem_cubicTorusOpenClusterFromFinset {d N : ℕ} (hN : 2 ≤ N)
    {ω : CubicTorusEdgeConfiguration d N} {x y : CubicTorus d N} :
    y ∈ cubicTorusOpenClusterFromFinset d N hN ω x ↔
      y ∈ cubicTorusOpenClusterFrom d N ω x := by
  rw [cubicTorusOpenClusterFromFinset, mem_restrictTo]
  simp [mem_cubicTorusVertexFinset hN]

theorem cubicTorusOpenClusterFromFinset_origin
    (d N : ℕ) (hN : 2 ≤ N) (ω : CubicTorusEdgeConfiguration d N) :
    cubicTorusOpenClusterFromFinset d N hN ω (cubicTorusOrigin d N) =
      cubicTorusOpenClusterFinset d N hN ω := by
  rfl

theorem cubicTorusOpenClusterFromFinset_map_translation
    {d N : ℕ} (hN : 2 ≤ N) (z x : CubicTorus d N)
    (s : Finset (CubicTorusEdge d N)) :
    (cubicTorusOpenClusterFromFinset d N hN (s : Set (CubicTorusEdge d N)) x).map
        (cubicTorusTranslationIso hN z).toEquiv.toEmbedding =
      cubicTorusOpenClusterFromFinset d N hN
        ((s.map (cubicTorusTranslationIso hN z).mapEdgeSet.toEmbedding :
          Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
        (cubicTorusTranslate z x) := by
  let f := cubicTorusTranslationIso hN z
  ext y
  constructor
  · intro hy
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_map.mp hy
    rw [mem_cubicTorusOpenClusterFromFinset] at hy₀ ⊢
    rcases hy₀ with ⟨w, hw⟩
    exact ⟨w.map f.toHom, torusWalkIsOpen_map_iso f s w hw⟩
  · intro hy
    rw [mem_cubicTorusOpenClusterFromFinset] at hy
    rcases hy with ⟨w, hw⟩
    let w₀ := w.map f.symm.toHom
    have hw₀ : torusWalkIsOpen
        (((s.map f.mapEdgeSet.toEmbedding).map f.symm.mapEdgeSet.toEmbedding :
          Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N)) w₀ :=
      torusWalkIsOpen_map_iso f.symm (s.map f.mapEdgeSet.toEmbedding) w hw
    have hedge : (s.map f.mapEdgeSet.toEmbedding).map f.symm.mapEdgeSet.toEmbedding = s := by
      ext e
      constructor
      · intro he
        obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hg
        have hback : f.symm.mapEdgeSet (f.mapEdgeSet k) = k :=
          f.mapEdgeSet.symm_apply_apply k
        change f.symm.mapEdgeSet (f.mapEdgeSet k) ∈ s
        rw [hback]
        exact hk
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨f.mapEdgeSet e, Finset.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
        exact f.mapEdgeSet.symm_apply_apply e
    rw [hedge] at hw₀
    have hx : f.symm (cubicTorusTranslate z x) = x := f.symm_apply_apply x
    let w₁ : (cubicTorusGraph d N).Walk x (f.symm y) :=
      w₀.copy hx rfl
    have hw₁ : torusWalkIsOpen (s : Set (CubicTorusEdge d N)) w₁ := by
      intro e he
      apply hw₀ e
      simpa [w₁, SimpleGraph.Walk.edges_copy] using he
    apply Finset.mem_map.mpr
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [mem_cubicTorusOpenClusterFromFinset]
    exact ⟨w₁, hw₁⟩

theorem cubicTorusOpenClusterFromFinset_card_map_translation
    {d N : ℕ} (hN : 2 ≤ N) (z x : CubicTorus d N)
    (s : Finset (CubicTorusEdge d N)) :
    (cubicTorusOpenClusterFromFinset d N hN
        ((s.map (cubicTorusTranslationIso hN z).mapEdgeSet.toEmbedding :
          Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
        (cubicTorusTranslate z x)).card =
      (cubicTorusOpenClusterFromFinset d N hN
        (s : Set (CubicTorusEdge d N)) x).card := by
  rw [← cubicTorusOpenClusterFromFinset_map_translation hN z x s, Finset.card_map]

theorem finiteBernoulliExpectation_inv_torusOpenCluster_card_eq_series
    (d N : ℕ) (hN : 2 ≤ N) (p : I) :
    finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) (p : ℝ)
        (fun s ↦ 1 / ((cubicTorusOpenClusterFinset d N hN
          (s : Set (CubicTorusEdge d N))).card : ℝ)) =
      torusClusterDensitySeries d N hN p := by
  have hsum := torusFiniteBernoulliExpectation_eq_sum_clusterSizes d N hN (p : ℝ)
    (fun n ↦ 1 / (n : ℝ))
  rw [hsum, torusClusterDensitySeries]
  simp_rw [← torusFiniteClusterSizeProbability_eq_finiteBernoulliProbability d N hN p]
  symm
  apply tsum_eq_sum
  intro n hn
  have hnlarge : (cubicTorusVertexFinset d N hN).card < n := by
    simpa only [Finset.mem_range, not_lt] using hn
  rw [torusFiniteClusterSizeProbability_eq_zero_of_large d N hN p hnlarge, mul_zero]

theorem finiteBernoulliExpectation_inv_torusOpenClusterFrom_card_eq_origin
    (d N : ℕ) (hN : 2 ≤ N) (p : ℝ) (x : CubicTorus d N) :
    finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p
        (fun s ↦ 1 / ((cubicTorusOpenClusterFromFinset d N hN
          (s : Set (CubicTorusEdge d N)) x).card : ℝ)) =
      finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p
        (fun s ↦ 1 / ((cubicTorusOpenClusterFinset d N hN
          (s : Set (CubicTorusEdge d N))).card : ℝ)) := by
  let f := cubicTorusTranslationIso hN x
  have hE : (cubicTorusEdgeFinset d N hN).map f.mapEdgeSet.toEmbedding =
      cubicTorusEdgeFinset d N hN := by
    ext e
    simp [mem_cubicTorusEdgeFinset hN]
  let X : Finset (CubicTorusEdge d N) → ℝ := fun s ↦
    1 / ((cubicTorusOpenClusterFromFinset d N hN
      (s : Set (CubicTorusEdge d N)) x).card : ℝ)
  have hmap := finiteBernoulliExpectation_map_equiv
    (cubicTorusEdgeFinset d N hN) p f.mapEdgeSet hE X
  have hx : cubicTorusTranslate x (cubicTorusOrigin d N) = x := by
    ext i
    simp [cubicTorusTranslate, cubicTorusOrigin]
  have hfun : (fun s : Finset (CubicTorusEdge d N) ↦
      X (s.map f.mapEdgeSet.toEmbedding)) =
      fun s : Finset (CubicTorusEdge d N) ↦ 1 / ((cubicTorusOpenClusterFinset d N hN
        (s : Set (CubicTorusEdge d N))).card : ℝ) := by
    funext s
    dsimp only [X]
    rw [← hx, cubicTorusOpenClusterFromFinset_card_map_translation
      hN x (cubicTorusOrigin d N) s,
      cubicTorusOpenClusterFromFinset_origin]
  rw [hfun] at hmap
  exact hmap.symm

/-! ### Periodic component counts -/

def cubicTorusOpenGraph (d N : ℕ) (ω : CubicTorusEdgeConfiguration d N) :
    SimpleGraph (CubicTorus d N) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (cubicTorusGraph d N).edgeSet,
      (⟨e, h⟩ : CubicTorusEdge d N) ∈ ω}

theorem cubicTorusOpenGraph_adj {d N : ℕ} {ω : CubicTorusEdgeConfiguration d N}
    {x y : CubicTorus d N} :
    (cubicTorusOpenGraph d N ω).Adj x y ↔
      ∃ h : (cubicTorusGraph d N).Adj x y,
        (⟨s(x, y), (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr h⟩ :
          CubicTorusEdge d N) ∈ ω := by
  simp only [cubicTorusOpenGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, ne_eq]
  constructor
  · rintro ⟨⟨h, hopen⟩, _hxy⟩
    exact ⟨(SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mp h, hopen⟩
  · rintro ⟨h, hopen⟩
    exact ⟨⟨(SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr h, hopen⟩, h.ne⟩

def cubicTorusOpenGraphHom (d N : ℕ) (ω : CubicTorusEdgeConfiguration d N) :
    cubicTorusOpenGraph d N ω →g cubicTorusGraph d N where
  toFun := id
  map_rel' := fun h ↦ (cubicTorusOpenGraph_adj.mp h).choose

theorem torusWalkIsOpen_map_cubicTorusOpenGraphHom
    {d N : ℕ} {ω : CubicTorusEdgeConfiguration d N}
    {x y : CubicTorus d N} (w : (cubicTorusOpenGraph d N ω).Walk x y) :
    torusWalkIsOpen ω (w.map (cubicTorusOpenGraphHom d N ω)) := by
  induction w with
  | nil =>
      intro e he
      simp at he
  | @cons u v y huv q ih =>
      intro e he
      simp only [SimpleGraph.Walk.map_cons, SimpleGraph.Walk.edges_cons,
        List.mem_cons] at he
      rcases he with he | he
      · subst e
        simpa [cubicTorusOpenGraphHom] using (cubicTorusOpenGraph_adj.mp huv).choose_spec
      · exact ih e he

theorem nonempty_cubicTorusOpenGraph_walk_of_torusWalkIsOpen
    {d N : ℕ} {ω : CubicTorusEdgeConfiguration d N}
    {x y : CubicTorus d N} (w : (cubicTorusGraph d N).Walk x y)
    (hopen : torusWalkIsOpen ω w) :
    Nonempty ((cubicTorusOpenGraph d N ω).Walk x y) := by
  induction w with
  | nil => exact ⟨.nil⟩
  | @cons u v y huv q ih =>
      have hopenTail : torusWalkIsOpen ω q := by
        intro e he
        exact hopen e (by simp [SimpleGraph.Walk.edges_cons, he])
      rcases ih hopenTail with ⟨r⟩
      have hopenHead :
          (⟨s(u, v), (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr huv⟩ :
            CubicTorusEdge d N) ∈ ω := by
        apply hopen
        simp [SimpleGraph.Walk.edges_cons]
      exact ⟨SimpleGraph.Walk.cons (cubicTorusOpenGraph_adj.mpr ⟨huv, hopenHead⟩) r⟩

theorem cubicTorusOpenGraph_reachable_iff
    {d N : ℕ} {ω : CubicTorusEdgeConfiguration d N} {x y : CubicTorus d N} :
    (cubicTorusOpenGraph d N ω).Reachable x y ↔
      y ∈ cubicTorusOpenClusterFrom d N ω x := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.map (cubicTorusOpenGraphHom d N ω),
      torusWalkIsOpen_map_cubicTorusOpenGraphHom w⟩
  · rintro ⟨w, hw⟩
    exact nonempty_cubicTorusOpenGraph_walk_of_torusWalkIsOpen w hw

theorem cubicTorusOpenGraph_component_supp
    {d N : ℕ} {ω : CubicTorusEdgeConfiguration d N} (x : CubicTorus d N) :
    ((cubicTorusOpenGraph d N ω).connectedComponentMk x).supp =
      cubicTorusOpenClusterFrom d N ω x := by
  ext y
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · intro h
    exact cubicTorusOpenGraph_reachable_iff.mp (SimpleGraph.ConnectedComponent.eq.mp h).symm
  · intro h
    exact SimpleGraph.ConnectedComponent.eq.mpr (cubicTorusOpenGraph_reachable_iff.mpr h).symm

theorem componentSize_cubicTorusOpenGraph
    {d N : ℕ} (hN : 2 ≤ N) {ω : CubicTorusEdgeConfiguration d N}
    (x : CubicTorus d N) :
    componentSize (cubicTorusOpenGraph d N ω) x =
      (cubicTorusOpenClusterFromFinset d N hN ω x).card := by
  rw [componentSize, Nat.card_coe_set_eq, cubicTorusOpenGraph_component_supp,
    ← Set.ncard_coe_finset (cubicTorusOpenClusterFromFinset d N hN ω x)]
  congr 1
  ext y
  simp [mem_cubicTorusOpenClusterFromFinset]

def torusNormalizedComponentCountTrace
    (d N : ℕ) (hN : 2 ≤ N) (s : Finset (CubicTorusEdge d N)) : ℝ :=
  (Nat.card (cubicTorusOpenGraph d N (s : Set (CubicTorusEdge d N))).ConnectedComponent : ℝ) /
    (cubicTorusVertexFinset d N hN).card

theorem torusNormalizedComponentCountTrace_eq_average
    (d N : ℕ) (hN : 2 ≤ N) (s : Finset (CubicTorusEdge d N)) :
    torusNormalizedComponentCountTrace d N hN s =
      (1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) *
        ∑ x ∈ cubicTorusVertexFinset d N hN,
          1 / ((cubicTorusOpenClusterFromFinset d N hN
            (s : Set (CubicTorusEdge d N)) x).card : ℝ) := by
  letI : NeZero (2 * N) := ⟨by omega⟩
  have hsum := sum_componentWeight_eq_componentCount
    (cubicTorusOpenGraph d N (s : Set (CubicTorusEdge d N)))
  simp_rw [componentWeight, componentSize_cubicTorusOpenGraph hN] at hsum
  rw [torusNormalizedComponentCountTrace, ← hsum]
  have hfinset : cubicTorusVertexFinset d N hN = Finset.univ := by
    unfold cubicTorusVertexFinset
    rfl
  rw [hfinset]
  change (∑ x : CubicTorus d N,
      1 / ((cubicTorusOpenClusterFromFinset d N hN
        (s : Set (CubicTorusEdge d N)) x).card : ℝ)) /
      (Fintype.card (CubicTorus d N) : ℝ) =
    (1 / (Fintype.card (CubicTorus d N) : ℝ)) *
      ∑ x : CubicTorus d N,
        1 / ((cubicTorusOpenClusterFromFinset d N hN
          (s : Set (CubicTorusEdge d N)) x).card : ℝ)
  ring

theorem finiteBernoulliExpectation_torusNormalizedComponentCountTrace_eq_series
    (d N : ℕ) (hN : 2 ≤ N) (p : I) :
    finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) (p : ℝ)
        (torusNormalizedComponentCountTrace d N hN) =
      torusClusterDensitySeries d N hN p := by
  let E := cubicTorusEdgeFinset d N hN
  let V := cubicTorusVertexFinset d N hN
  have havg : (fun s ↦ torusNormalizedComponentCountTrace d N hN s) =
      fun s : Finset (CubicTorusEdge d N) ↦ (1 / (V.card : ℝ)) *
        ∑ x ∈ V,
          1 / ((cubicTorusOpenClusterFromFinset d N hN
            (s : Set (CubicTorusEdge d N)) x).card : ℝ) := by
    funext s
    exact torusNormalizedComponentCountTrace_eq_average d N hN s
  rw [show torusNormalizedComponentCountTrace d N hN =
      fun s ↦ torusNormalizedComponentCountTrace d N hN s from rfl, havg,
    finiteBernoulliExpectation_const_mul,
    finiteBernoulliExpectation_finset_sum]
  simp_rw [finiteBernoulliExpectation_inv_torusOpenClusterFrom_card_eq_origin d N hN (p : ℝ)]
  rw [Finset.sum_const, nsmul_eq_mul,
    finiteBernoulliExpectation_inv_torusOpenCluster_card_eq_series d N hN p]
  have hpos : (0 : ℝ) < V.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨cubicTorusOrigin d N, mem_cubicTorusVertexFinset hN _⟩
  field_simp

theorem sym2_mk_out {α : Type*} (e : Sym2 α) :
    s(e.out.1, e.out.2) = e := by
  exact Quot.out_eq e

theorem cubicTorusEdge_out_ne {d N : ℕ} (e : CubicTorusEdge d N) :
    e.1.out.1 ≠ e.1.out.2 := by
  have hadj : (cubicTorusGraph d N).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet, sym2_mk_out]
    exact e.2
  exact hadj.ne

def cubicTorusReverseDirection {d : ℕ} (a : CubicDirection d) : CubicDirection d :=
  (a.1, !a.2)

theorem cubicTorusStepFrom_reverse {d N : ℕ} (x : CubicTorus d N)
    (a : CubicDirection d) :
    cubicTorusStepFrom (cubicTorusStepFrom x a) (cubicTorusReverseDirection a) = x := by
  rcases a with ⟨i, b⟩
  ext j
  by_cases hji : j = i
  · subst j
    cases b <;> simp [cubicTorusReverseDirection, cubicTorusStepFrom]
  · simp [cubicTorusReverseDirection, cubicTorusStepFrom, Function.update_of_ne hji]

theorem cubicTorusStepFrom_comm_of_axis_ne {d N : ℕ} (x : CubicTorus d N)
    {a c : CubicDirection d} (hac : a.1 ≠ c.1) :
    cubicTorusStepFrom (cubicTorusStepFrom x a) c =
      cubicTorusStepFrom (cubicTorusStepFrom x c) a := by
  rcases a with ⟨i, b⟩
  rcases c with ⟨j, t⟩
  dsimp only at hac
  ext k
  by_cases hki : k = i
  · subst k
    rw [cubicTorusStepFrom_apply_of_ne _ hac t,
      cubicTorusStepFrom_apply_same,
      cubicTorusStepFrom_apply_same,
      cubicTorusStepFrom_apply_of_ne _ hac t]
  · by_cases hkj : k = j
    · subst k
      rw [cubicTorusStepFrom_apply_same,
        cubicTorusStepFrom_apply_of_ne _ hac.symm b,
        cubicTorusStepFrom_apply_of_ne _ hac.symm b,
        cubicTorusStepFrom_apply_same]
    · rw [cubicTorusStepFrom_apply_of_ne _ hkj t,
        cubicTorusStepFrom_apply_of_ne _ hki b,
        cubicTorusStepFrom_apply_of_ne _ hki b,
        cubicTorusStepFrom_apply_of_ne _ hkj t]

theorem cubicTorusStepEdge_injective_direction {d N : ℕ} (hN : 2 ≤ N)
    (x : CubicTorus d N) : Function.Injective (cubicTorusStepEdge hN x) := by
  intro a c hac
  have hval := congrArg Subtype.val hac
  rcases Sym2.eq_iff.mp hval with h | h
  · exact cubicTorusStepFrom_injective_direction hN x h.2
  · exact (cubicTorusStepFrom_ne_self hN x a h.2).elim

theorem cubicTorusStepEdge_reverse {d N : ℕ} (hN : 2 ≤ N)
    (x : CubicTorus d N) (a : CubicDirection d) :
    cubicTorusStepEdge hN (cubicTorusStepFrom x a) (cubicTorusReverseDirection a) =
      cubicTorusStepEdge hN x a := by
  apply Subtype.ext
  change s(cubicTorusStepFrom x a,
      cubicTorusStepFrom (cubicTorusStepFrom x a) (cubicTorusReverseDirection a)) =
    s(x, cubicTorusStepFrom x a)
  rw [cubicTorusStepFrom_reverse]
  exact Sym2.eq_swap

noncomputable def cubicTorusPerpendicularAxis {d : ℕ} (hd : 2 ≤ d) (i : Fin d) : Fin d :=
  by
    letI : Nontrivial (Fin d) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
    exact Classical.choose (exists_ne i)

theorem cubicTorusPerpendicularAxis_ne {d : ℕ} (hd : 2 ≤ d) (i : Fin d) :
    cubicTorusPerpendicularAxis hd i ≠ i :=
  by
    letI : Nontrivial (Fin d) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
    exact Classical.choose_spec (exists_ne i)

structure CubicTorusEdgeDetour (d N : ℕ) (hN : 2 ≤ N) where
  edge : CubicTorusEdge d N
  support : Finset (CubicTorusEdge d N)
  card_le_three : support.card ≤ 3
  edge_not_mem : edge ∉ support
  reachable : (cubicTorusOpenGraph d N (support : Set (CubicTorusEdge d N))).Reachable
    edge.1.out.1 edge.1.out.2

noncomputable def cubicTorusEdgeDetour {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N)
    (e : CubicTorusEdge d N) : CubicTorusEdgeDetour d N hN := by
  let u := e.1.out.1
  let v := e.1.out.2
  have huv : (cubicTorusGraph d N).Adj u v := by
    rw [← SimpleGraph.mem_edgeSet, sym2_mk_out]
    exact e.2
  let a := Classical.choose ((cubicTorusGraph_adj_iff_exists_stepFrom hN u v).mp huv)
  have hv : v = cubicTorusStepFrom u a :=
    Classical.choose_spec ((cubicTorusGraph_adj_iff_exists_stepFrom hN u v).mp huv)
  let j := cubicTorusPerpendicularAxis hd a.1
  let c : CubicDirection d := (j, true)
  have hac : a.1 ≠ c.1 := by
    dsimp only [c, j]
    exact (cubicTorusPerpendicularAxis_ne hd a.1).symm
  let uc := cubicTorusStepFrom u c
  let vc := cubicTorusStepFrom v c
  have huc : (cubicTorusGraph d N).Adj u uc := cubicTorusGraph_adj_stepFrom hN u c
  have hucvc : (cubicTorusGraph d N).Adj uc vc := by
    dsimp only [vc]
    rw [hv]
    change (cubicTorusGraph d N).Adj (cubicTorusStepFrom u c)
      (cubicTorusStepFrom (cubicTorusStepFrom u a) c)
    rw [cubicTorusStepFrom_comm_of_axis_ne u hac]
    exact cubicTorusGraph_adj_stepFrom hN (cubicTorusStepFrom u c) a
  have hvc_eq : cubicTorusStepFrom uc a = vc := by
    dsimp only [uc, vc]
    rw [hv, cubicTorusStepFrom_comm_of_axis_ne u hac]
  have hvc : (cubicTorusGraph d N).Adj vc v :=
    (cubicTorusGraph_adj_stepFrom hN v c).symm
  let e1 := cubicTorusStepEdge hN u c
  let e2 := cubicTorusStepEdge hN uc a
  let e3 := cubicTorusStepEdge hN v c
  have he : cubicTorusStepEdge hN u a = e := by
    apply Subtype.ext
    change s(u, cubicTorusStepFrom u a) = e.1
    rw [← hv, sym2_mk_out]
  have he1 : e1 ≠ e := by
    intro h
    have hca : c = a := cubicTorusStepEdge_injective_direction hN u
      (h.trans he.symm)
    exact hac (congrArg Prod.fst hca).symm
  have he3 : e3 ≠ e := by
    intro h
    have hrev : cubicTorusStepEdge hN v (cubicTorusReverseDirection a) = e := by
      rw [hv, cubicTorusStepEdge_reverse, he]
    have hcEq : c = cubicTorusReverseDirection a :=
      cubicTorusStepEdge_injective_direction hN v (h.trans hrev.symm)
    exact hac (congrArg Prod.fst hcEq).symm
  have he2 : e2 ≠ e := by
    intro h
    have hval := congrArg Subtype.val (h.trans he.symm)
    change s(uc, cubicTorusStepFrom uc a) = s(u, cubicTorusStepFrom u a) at hval
    rcases Sym2.eq_iff.mp hval with hdir | hswap
    · exact (cubicTorusStepFrom_ne_self hN u c hdir.1).elim
    · have hca : c = a := cubicTorusStepFrom_injective_direction hN u hswap.1
      exact hac (congrArg Prod.fst hca).symm
  let T : Finset (CubicTorusEdge d N) := {e1, e2, e3}
  refine
    { edge := e
      support := T
      card_le_three := by
        have h1 := Finset.card_insert_le e1 ({e2, e3} : Finset (CubicTorusEdge d N))
        have h2 := Finset.card_insert_le e2 ({e3} : Finset (CubicTorusEdge d N))
        have h3 : ({e3} : Finset (CubicTorusEdge d N)).card ≤ 1 := by simp
        dsimp only [T]
        omega
      edge_not_mem := by
        simp only [T, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨he1.symm, he2.symm, he3.symm⟩
      reachable := ?_ }
  let w : (cubicTorusGraph d N).Walk u v :=
    .cons huc (.cons hucvc (.cons hvc .nil))
  have hw : torusWalkIsOpen (T : Set (CubicTorusEdge d N)) w := by
    intro g hg
    simp only [w, SimpleGraph.Walk.edges_cons, List.mem_cons,
      SimpleGraph.Walk.edges_nil, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg
    · have hge : (⟨g, w.edges_subset_edgeSet (by simp [w, hg])⟩ : CubicTorusEdge d N) = e1 := by
        apply Subtype.ext
        simpa [e1, cubicTorusStepEdge, uc] using hg
      simp [T, hge]
    · have hge : (⟨g, w.edges_subset_edgeSet (by simp [w, hg])⟩ : CubicTorusEdge d N) = e2 := by
        apply Subtype.ext
        change g = s(uc, cubicTorusStepFrom uc a)
        rw [hvc_eq]
        exact hg
      simp [T, hge]
    · have hge : (⟨g, w.edges_subset_edgeSet (by simp [w, hg])⟩ : CubicTorusEdge d N) = e3 := by
        apply Subtype.ext
        change g = s(v, vc)
        exact hg.trans Sym2.eq_swap
      simp [T, hge]
  change (cubicTorusOpenGraph d N (T : Set _)).Reachable u v
  exact cubicTorusOpenGraph_reachable_iff.mpr ⟨w, hw⟩

theorem cubicTorusOpenGraph_insert_eq_sup_edge
    {d N : ℕ} (s : Finset (CubicTorusEdge d N)) (e : CubicTorusEdge d N) :
    cubicTorusOpenGraph d N
        ((insert e s : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N)) =
      cubicTorusOpenGraph d N
          ((s.erase e : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N)) ⊔
        SimpleGraph.edge e.1.out.1 e.1.out.2 := by
  ext x y
  rw [cubicTorusOpenGraph_adj, SimpleGraph.sup_adj, cubicTorusOpenGraph_adj,
    SimpleGraph.edge_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    have hopen' : (⟨s(x, y),
        (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr hxy⟩ :
          CubicTorusEdge d N) = e ∨
        (⟨s(x, y), (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr hxy⟩ :
          CubicTorusEdge d N) ∈ s := by simpa using hopen
    rcases hopen' with heq | hs
    · right
      have hval := congrArg Subtype.val heq
      rw [← sym2_mk_out e.1] at hval
      exact ⟨Sym2.eq_iff.mp hval, hxy.ne⟩
    · by_cases heq : (⟨s(x, y),
          (SimpleGraph.mem_edgeSet (cubicTorusGraph d N)).mpr hxy⟩ :
            CubicTorusEdge d N) = e
      · right
        have hval := congrArg Subtype.val heq
        rw [← sym2_mk_out e.1] at hval
        exact ⟨Sym2.eq_iff.mp hval, hxy.ne⟩
      · left
        exact ⟨hxy, Finset.mem_erase.mpr ⟨heq, hs⟩⟩
  · rintro (⟨hxy, hopen⟩ | ⟨hxy, _hne⟩)
    · exact ⟨hxy, by
        apply Finset.mem_insert.mpr
        exact Or.inr (Finset.mem_of_mem_erase hopen)⟩
    · have hval : s(x, y) = e.1 := by
        exact (Sym2.eq_iff.mpr hxy).trans (sym2_mk_out e.1)
      have hxyGraph : (cubicTorusGraph d N).Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, hval]
        exact e.2
      refine ⟨hxyGraph, ?_⟩
      apply Finset.mem_insert.mpr
      left
      apply Subtype.ext
      exact hval

theorem traceDifference_torusNormalizedComponentCountTrace_le_zero
    (d N : ℕ) (hN : 2 ≤ N) (e : CubicTorusEdge d N)
    (s : Finset (CubicTorusEdge d N)) :
    traceDifference e (torusNormalizedComponentCountTrace d N hN) s ≤ 0 := by
  let G := cubicTorusOpenGraph d N
    ((s.erase e : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
  let H := cubicTorusOpenGraph d N
    ((insert e s : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
  have hGH : G ≤ H := by
    rw [show H = G ⊔ SimpleGraph.edge e.1.out.1 e.1.out.2 from
      cubicTorusOpenGraph_insert_eq_sup_edge s e]
    exact le_sup_left
  letI : NeZero (2 * N) := ⟨by omega⟩
  have hcard := SimpleGraph.ConnectedComponent.card_le_card_of_le hGH
  unfold traceDifference torusNormalizedComponentCountTrace
  dsimp only [G, H] at hcard
  have hV : (0 : ℝ) ≤ (cubicTorusVertexFinset d N hN).card := by positivity
  have hcardR :
      (Nat.card (cubicTorusOpenGraph d N
        ((insert e s : Finset (CubicTorusEdge d N)) : Set _)).ConnectedComponent : ℝ) ≤
      Nat.card (cubicTorusOpenGraph d N
        ((s.erase e : Finset (CubicTorusEdge d N)) : Set _)).ConnectedComponent := by
    exact_mod_cast hcard
  rw [← sub_div]
  rw [finset_erase_classical_eq, finset_insert_classical_eq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcardR) hV

theorem neg_one_div_card_le_traceDifference_torusNormalizedComponentCountTrace
    (d N : ℕ) (hN : 2 ≤ N) (e : CubicTorusEdge d N)
    (s : Finset (CubicTorusEdge d N)) :
    -(1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) ≤
      traceDifference e (torusNormalizedComponentCountTrace d N hN) s := by
  let G := cubicTorusOpenGraph d N
    ((s.erase e : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
  let H := cubicTorusOpenGraph d N
    ((insert e s : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
  have hH : H = G ⊔ SimpleGraph.edge e.1.out.1 e.1.out.2 :=
    cubicTorusOpenGraph_insert_eq_sup_edge s e
  letI : NeZero (2 * N) := ⟨by omega⟩
  have hcard := connectedComponent_card_le_add_one_sup_edge G (cubicTorusEdge_out_ne e)
  rw [← hH] at hcard
  unfold traceDifference torusNormalizedComponentCountTrace
  dsimp only [G, H] at hcard
  have hV : (0 : ℝ) < (cubicTorusVertexFinset d N hN).card := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨cubicTorusOrigin d N, mem_cubicTorusVertexFinset hN _⟩
  rw [neg_le_sub_iff_le_add]
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right hV).2
  rw [finset_erase_classical_eq, finset_insert_classical_eq]
  exact_mod_cast hcard

theorem cubicTorusOpenGraph_mono {d N : ℕ}
    {ω η : CubicTorusEdgeConfiguration d N} (hωη : ω ⊆ η) :
    cubicTorusOpenGraph d N ω ≤ cubicTorusOpenGraph d N η := by
  intro x y hxy
  rcases cubicTorusOpenGraph_adj.mp hxy with ⟨h, hopen⟩
  exact cubicTorusOpenGraph_adj.mpr ⟨h, hωη hopen⟩

theorem traceDifference_torusNormalizedComponentCountTrace_eq_zero_of_detour_subset
    {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) (e : CubicTorusEdge d N)
    (s : Finset (CubicTorusEdge d N))
    (hsub : (cubicTorusEdgeDetour hd hN e).support ⊆ s) :
    traceDifference e (torusNormalizedComponentCountTrace d N hN) s = 0 := by
  let D := cubicTorusEdgeDetour hd hN e
  let G := cubicTorusOpenGraph d N
    ((s.erase e : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
  let H := cubicTorusOpenGraph d N
    ((insert e s : Finset (CubicTorusEdge d N)) : Set (CubicTorusEdge d N))
  have hDsub : D.support ⊆ s.erase e := by
    intro f hf
    exact Finset.mem_erase.mpr ⟨(fun hfe ↦ by
      subst f
      apply D.edge_not_mem
      simpa [D] using hf), hsub hf⟩
  have hreach : G.Reachable e.1.out.1 e.1.out.2 :=
    D.reachable.mono (cubicTorusOpenGraph_mono (Finset.coe_subset.mpr hDsub))
  have hH : H = G ⊔ SimpleGraph.edge e.1.out.1 e.1.out.2 :=
    cubicTorusOpenGraph_insert_eq_sup_edge s e
  letI : NeZero (2 * N) := ⟨by omega⟩
  have hcard := connectedComponent_card_sup_edge_eq_of_reachable G
    (cubicTorusEdge_out_ne e) hreach
  rw [← hH] at hcard
  unfold traceDifference torusNormalizedComponentCountTrace
  dsimp only [G, H] at hcard
  apply sub_eq_zero.mpr
  congr 1
  rw [finset_insert_classical_eq, finset_erase_classical_eq]
  exact_mod_cast hcard

def closedCoordinate {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι) : ℝ :=
  if a ∈ s then 0 else 1

theorem finiteBernoulliExpectation_closedCoordinate
    {ι : Type*} [DecidableEq ι] {E : Finset ι} {a : ι} (ha : a ∈ E) (p : ℝ) :
    finiteBernoulliExpectation E p (closedCoordinate a) = 1 - p := by
  have hsplit := finiteBernoulliExpectation_insert (Finset.notMem_erase a E) p
    (closedCoordinate a)
  have hsplit' : finiteBernoulliExpectation E p (closedCoordinate a) =
      p * finiteBernoulliExpectation (E.erase a) p
          (fun s ↦ closedCoordinate a (insert a s)) +
        (1 - p) * finiteBernoulliExpectation (E.erase a) p (closedCoordinate a) := by
    simpa only [finset_insert_classical_eq, Finset.insert_erase ha] using hsplit
  have hopen : finiteBernoulliExpectation (E.erase a) p
      (fun s ↦ closedCoordinate a (insert a s)) = 0 := by
    rw [show finiteBernoulliExpectation (E.erase a) p
        (fun s ↦ closedCoordinate a (insert a s)) =
        finiteBernoulliExpectation (E.erase a) p (fun _ ↦ 0) by
      apply finiteBernoulliExpectation_congr
      intro s hs
      simp [closedCoordinate]]
    exact finiteBernoulliExpectation_const _ _ _
  have hclosed : finiteBernoulliExpectation (E.erase a) p (closedCoordinate a) = 1 := by
    rw [show finiteBernoulliExpectation (E.erase a) p (closedCoordinate a) =
        finiteBernoulliExpectation (E.erase a) p (fun _ ↦ 1) by
      apply finiteBernoulliExpectation_congr
      intro s hs
      have hsa : a ∉ s := fun h ↦ Finset.notMem_erase a E
        (Finset.mem_powerset.mp hs h)
      simp [closedCoordinate, hsa]]
    exact finiteBernoulliExpectation_const _ _ _
  rw [hsplit', hopen, hclosed]
  ring

theorem neg_traceDifference_torusNormalizedComponentCountTrace_le_detour_closed_sum
    {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) (e : CubicTorusEdge d N)
    (s : Finset (CubicTorusEdge d N)) :
    -traceDifference e (torusNormalizedComponentCountTrace d N hN) s ≤
      (1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) *
        ∑ f ∈ (cubicTorusEdgeDetour hd hN e).support, closedCoordinate f s := by
  let D := cubicTorusEdgeDetour hd hN e
  have hV : (0 : ℝ) < (cubicTorusVertexFinset d N hN).card := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨cubicTorusOrigin d N, mem_cubicTorusVertexFinset hN _⟩
  by_cases hsub : D.support ⊆ s
  · rw [traceDifference_torusNormalizedComponentCountTrace_eq_zero_of_detour_subset
      hd hN e s hsub, neg_zero]
    exact mul_nonneg (one_div_nonneg.mpr hV.le) (Finset.sum_nonneg fun g _ ↦ by
      by_cases h : g ∈ s <;> simp [closedCoordinate, h])
  · obtain ⟨f, hfD, hfs⟩ := Finset.not_subset.mp hsub
    have hone : (1 : ℝ) ≤ ∑ g ∈ D.support, closedCoordinate g s := by
      calc
        (1 : ℝ) = closedCoordinate f s := by simp [closedCoordinate, hfs]
        _ ≤ ∑ g ∈ D.support, closedCoordinate g s := by
          apply Finset.single_le_sum (fun g _ ↦ by
            by_cases h : g ∈ s <;> simp [closedCoordinate, h]) hfD
    have htrace := neg_le_neg
      (neg_one_div_card_le_traceDifference_torusNormalizedComponentCountTrace d N hN e s)
    calc
      -traceDifference e (torusNormalizedComponentCountTrace d N hN) s ≤
          1 / ((cubicTorusVertexFinset d N hN).card : ℝ) := by simpa using htrace
      _ ≤ (1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) *
          ∑ g ∈ D.support, closedCoordinate g s := by
        simpa using mul_le_mul_of_nonneg_left hone (one_div_nonneg.mpr hV.le)

theorem finiteBernoulliExpectation_neg_traceDifference_torusNormalizedComponentCountTrace_le
    {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) (p : I) (e : CubicTorusEdge d N) :
    finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) (p : ℝ)
        (fun s ↦ -traceDifference e (torusNormalizedComponentCountTrace d N hN) s) ≤
      3 * (1 - (p : ℝ)) /
        (cubicTorusVertexFinset d N hN).card := by
  let E := cubicTorusEdgeFinset d N hN
  let D := cubicTorusEdgeDetour hd hN e
  have hmono := finiteBernoulliExpectation_mono (E := E) p.2.1 p.2.2 (fun s _hs ↦
    neg_traceDifference_torusNormalizedComponentCountTrace_le_detour_closed_sum
      hd hN e s)
  have hsupport : ∀ f ∈ D.support, f ∈ E := by
    intro f _hf
    exact mem_cubicTorusEdgeFinset hN f
  have hrw : finiteBernoulliExpectation E (p : ℝ)
      (fun s ↦ (1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) *
        ∑ f ∈ D.support, closedCoordinate f s) =
      (1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) *
        (D.support.card : ℝ) * (1 - (p : ℝ)) := by
    rw [finiteBernoulliExpectation_const_mul,
      finiteBernoulliExpectation_finset_sum]
    rw [show (∑ f ∈ D.support,
        finiteBernoulliExpectation E (p : ℝ) (closedCoordinate f)) =
        ∑ _f ∈ D.support, (1 - (p : ℝ)) by
      apply Finset.sum_congr rfl
      intro f hf
      exact finiteBernoulliExpectation_closedCoordinate (p := (p : ℝ))
        (hsupport f hf)]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hrw] at hmono
  have hq : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hV : 0 ≤ 1 / ((cubicTorusVertexFinset d N hN).card : ℝ) := by positivity
  calc
    finiteBernoulliExpectation E (p : ℝ)
        (fun s ↦ -traceDifference e (torusNormalizedComponentCountTrace d N hN) s) ≤
        (1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) *
          (D.support.card : ℝ) * (1 - (p : ℝ)) := hmono
    _ ≤ (1 / ((cubicTorusVertexFinset d N hN).card : ℝ)) * 3 *
          (1 - (p : ℝ)) := by
      gcongr
      exact_mod_cast D.card_le_three
    _ = 3 * (1 - (p : ℝ)) /
          (cubicTorusVertexFinset d N hN).card := by ring

def torusNormalizedComponentCountExpectation
    (d N : ℕ) (hN : 2 ≤ N) (p : ℝ) : ℝ :=
  finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p
    (torusNormalizedComponentCountTrace d N hN)

theorem torusNormalizedComponentCountExpectation_eq_series
    (d N : ℕ) (hN : 2 ≤ N) (p : I) :
    torusNormalizedComponentCountExpectation d N hN p =
      torusClusterDensitySeries d N hN p :=
  finiteBernoulliExpectation_torusNormalizedComponentCountTrace_eq_series d N hN p

theorem torusNormalizedComponentCountExpectation_hasDerivAt
    (d N : ℕ) (hN : 2 ≤ N) (p : ℝ) :
    HasDerivAt (torusNormalizedComponentCountExpectation d N hN)
      (∑ e ∈ cubicTorusEdgeFinset d N hN,
        finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) p
          (traceDifference e (torusNormalizedComponentCountTrace d N hN))) p := by
  exact hasDerivAt_finiteBernoulliExpectation _ p

theorem cubicTorusEdgeFinset_card_le_vertex_card_mul_two_d
    (d N : ℕ) (hN : 2 ≤ N) :
    (cubicTorusEdgeFinset d N hN).card ≤
      (cubicTorusVertexFinset d N hN).card * (2 * d) := by
  have hEq : cubicTorusEdgeFinset d N hN =
      cubicTorusIncidentEdges d N hN (cubicTorusVertexFinset d N hN) := by
    ext e
    constructor
    · intro _he
      rw [mem_cubicTorusIncidentEdges]
      exact ⟨e.1.out.1, Sym2.out_fst_mem e.1,
        mem_cubicTorusVertexFinset hN _⟩
    · intro _he
      exact mem_cubicTorusEdgeFinset hN e
  rw [hEq]
  exact cubicTorusIncidentEdges_card_le d N hN _

theorem abs_torusNormalizedComponentCountExpectation_deriv_le
    {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) (p : I) :
    |∑ e ∈ cubicTorusEdgeFinset d N hN,
        finiteBernoulliExpectation (cubicTorusEdgeFinset d N hN) (p : ℝ)
          (traceDifference e (torusNormalizedComponentCountTrace d N hN))| ≤
      6 * d * (1 - (p : ℝ)) := by
  let E := cubicTorusEdgeFinset d N hN
  let V := cubicTorusVertexFinset d N hN
  let F : CubicTorusEdge d N → ℝ := fun e ↦
    finiteBernoulliExpectation E (p : ℝ)
      (traceDifference e (torusNormalizedComponentCountTrace d N hN))
  have hnonpos : ∀ e ∈ E, F e ≤ 0 := by
    intro e he
    calc
      F e ≤ finiteBernoulliExpectation E (p : ℝ) (fun _ ↦ 0) :=
        finiteBernoulliExpectation_mono p.2.1 p.2.2 (fun s hs ↦
          traceDifference_torusNormalizedComponentCountTrace_le_zero d N hN e s)
      _ = 0 := finiteBernoulliExpectation_const _ _ _
  have hlower : ∀ e ∈ E,
      -(3 * (1 - (p : ℝ)) / (V.card : ℝ)) ≤ F e := by
    intro e he
    have h := finiteBernoulliExpectation_neg_traceDifference_torusNormalizedComponentCountTrace_le
      hd hN p e
    have hneg : finiteBernoulliExpectation E (p : ℝ)
        (fun s ↦ -traceDifference e (torusNormalizedComponentCountTrace d N hN) s) =
        -F e := by
      rw [show (fun s ↦ -traceDifference e
          (torusNormalizedComponentCountTrace d N hN) s) =
          fun s ↦ (-1 : ℝ) * traceDifference e
            (torusNormalizedComponentCountTrace d N hN) s by funext s; ring,
        finiteBernoulliExpectation_const_mul]
      ring
    rw [hneg] at h
    linarith
  have hsumNonpos : ∑ e ∈ E, F e ≤ 0 := Finset.sum_nonpos hnonpos
  have hsumLower : E.card * (-(3 * (1 - (p : ℝ)) / (V.card : ℝ))) ≤
      ∑ e ∈ E, F e := by
    calc
      E.card * (-(3 * (1 - (p : ℝ)) / (V.card : ℝ))) =
          ∑ _e ∈ E, (-(3 * (1 - (p : ℝ)) / (V.card : ℝ))) := by simp
      _ ≤ ∑ e ∈ E, F e := Finset.sum_le_sum hlower
  have hVpos : (0 : ℝ) < V.card := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨cubicTorusOrigin d N, mem_cubicTorusVertexFinset hN _⟩
  have hcard := cubicTorusEdgeFinset_card_le_vertex_card_mul_two_d d N hN
  have hbound : -(6 * d * (1 - (p : ℝ))) ≤ ∑ e ∈ E, F e := by
    have hq : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
    have hcardR : (E.card : ℝ) ≤ (V.card : ℝ) * (2 * d : ℝ) := by
      exact_mod_cast hcard
    have hmul : (E.card : ℝ) * (3 * (1 - (p : ℝ)) / (V.card : ℝ)) ≤
        6 * d * (1 - (p : ℝ)) := by
      calc
        (E.card : ℝ) * (3 * (1 - (p : ℝ)) / (V.card : ℝ)) ≤
            ((V.card : ℝ) * (2 * d : ℝ)) *
              (3 * (1 - (p : ℝ)) / (V.card : ℝ)) := by gcongr
        _ = 6 * d * (1 - (p : ℝ)) := by field_simp; ring
    linarith
  rw [abs_of_nonpos hsumNonpos]
  simpa [E, V, F] using neg_le_neg hbound

theorem norm_torusNormalizedComponentCountExpectation_sub_le
    {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) {p q : I}
    (hpq : (p : ℝ) ≤ (q : ℝ)) :
    ‖torusNormalizedComponentCountExpectation d N hN q -
        torusNormalizedComponentCountExpectation d N hN p‖ ≤
      (6 * d * (1 - (p : ℝ))) * ‖(q : ℝ) - (p : ℝ)‖ := by
  let F := torusNormalizedComponentCountExpectation d N hN
  have hdiff : ∀ x ∈ Icc (p : ℝ) (q : ℝ), DifferentiableAt ℝ F x := by
    intro x hx
    exact (torusNormalizedComponentCountExpectation_hasDerivAt d N hN x).differentiableAt
  have hbound : ∀ x ∈ Icc (p : ℝ) (q : ℝ),
      ‖deriv F x‖ ≤ 6 * d * (1 - (p : ℝ)) := by
    intro x hx
    let xI : I := ⟨x, p.2.1.trans hx.1, hx.2.trans q.2.2⟩
    have hderiv := (torusNormalizedComponentCountExpectation_hasDerivAt
      d N hN x).deriv
    have hlocal := abs_torusNormalizedComponentCountExpectation_deriv_le hd hN xI
    have hxle : 1 - x ≤ 1 - (p : ℝ) := sub_le_sub_left hx.1 1
    rw [show (xI : ℝ) = x from rfl] at hlocal
    rw [hderiv]
    simpa [Real.norm_eq_abs] using hlocal.trans
      (mul_le_mul_of_nonneg_left hxle (by positivity : (0 : ℝ) ≤ 6 * d))
  exact (convex_Icc (p : ℝ) (q : ℝ)).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (Set.left_mem_Icc.mpr hpq) (Set.right_mem_Icc.mpr hpq)

theorem norm_openClustersPerVertex_sub_le
    {d : ℕ} (hd : 2 ≤ d) {p q : I} (hpq : (p : ℝ) ≤ (q : ℝ)) :
    ‖openClustersPerVertex d q - openClustersPerVertex d p‖ ≤
      (6 * d * (1 - (p : ℝ))) * ‖(q : ℝ) - (p : ℝ)‖ := by
  let F : ℕ → ℝ := fun j ↦
    torusNormalizedComponentCountExpectation d (j + 2) (by omega) q -
      torusNormalizedComponentCountExpectation d (j + 2) (by omega) p
  have hF : Tendsto F atTop
      (nhds (openClustersPerVertex d q - openClustersPerVertex d p)) := by
    have hq := torusClusterDensitySeries_tendsto_openClustersPerVertex_aux d q
    have hp := torusClusterDensitySeries_tendsto_openClustersPerVertex_aux d p
    have hq' : Tendsto (fun j ↦
        torusNormalizedComponentCountExpectation d (j + 2) (by omega) q)
        atTop (nhds (openClustersPerVertex d q)) := by
      simpa only [torusNormalizedComponentCountExpectation_eq_series] using hq
    have hp' : Tendsto (fun j ↦
        torusNormalizedComponentCountExpectation d (j + 2) (by omega) p)
        atTop (nhds (openClustersPerVertex d p)) := by
      simpa only [torusNormalizedComponentCountExpectation_eq_series] using hp
    exact hq'.sub hp'
  apply le_of_tendsto hF.norm
  exact Filter.Eventually.of_forall fun j ↦
    norm_torusNormalizedComponentCountExpectation_sub_le hd (by omega) hpq

theorem norm_concreteClusterDensitySeries_sub_le
    {d : ℕ} (hd : 2 ≤ d) {r x y : ℝ}
    (hr0 : 0 ≤ r) (hx : x ∈ Icc r 1) (hy : y ∈ Icc r 1) :
    ‖concreteClusterDensitySeries d y - concreteClusterDensitySeries d x‖ ≤
      (6 * d * (1 - r)) * ‖y - x‖ := by
  let xI : I := ⟨x, hr0.trans hx.1, hx.2⟩
  let yI : I := ⟨y, hr0.trans hy.1, hy.2⟩
  rw [concreteClusterDensitySeries_eq_openClustersPerVertex (by omega) xI,
    concreteClusterDensitySeries_eq_openClustersPerVertex (by omega) yI]
  rcases le_total x y with hxy | hyx
  · have h := norm_openClustersPerVertex_sub_le hd (p := xI) (q := yI) hxy
    have hxr : 1 - x ≤ 1 - r := sub_le_sub_left hx.1 1
    exact h.trans (by
      rw [show (xI : ℝ) = x from rfl, show (yI : ℝ) = y from rfl]
      gcongr)
  · rw [norm_sub_rev]
    have h := norm_openClustersPerVertex_sub_le hd (p := yI) (q := xI) hyx
    have hyr : 1 - y ≤ 1 - r := sub_le_sub_left hy.1 1
    rw [norm_sub_rev (y : ℝ) x]
    exact h.trans (by
      rw [show (xI : ℝ) = x from rfl, show (yI : ℝ) = y from rfl]
      gcongr)

/-! ### The small-density animal endpoint -/

theorem card_cubicBondAnimal_le_pow_two_three_d_n (d n : ℕ) :
    (Fintype.card (CubicBondAnimal d n) : ℝ) ≤ (2 : ℝ) ^ (3 * d * n) := by
  let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hprob := finiteClusterSizeProbability_le_one d half n
  rw [finiteClusterSizeProbability_eq_sum_animals] at hprob
  have hterm : ∀ A : CubicBondAnimal d n,
      (1 / 2 : ℝ) ^ (3 * d * n) ≤
        (half : ℝ) ^ A.edges.card * (1 - (half : ℝ)) ^ A.boundary.card := by
    intro A
    have hsum : A.edges.card + A.boundary.card ≤ 3 * d * n := by
      calc
        A.edges.card + A.boundary.card ≤ d * n + 2 * d * n :=
          Nat.add_le_add A.edges_card_upper A.boundary_card_le
        _ = 3 * d * n := by ring
    have hp := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) hsum
    rw [show (half : ℝ) = 1 / 2 from rfl,
      show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num, ← pow_add]
    exact hp
  have hcardWeight : (Fintype.card (CubicBondAnimal d n) : ℝ) *
      (1 / 2 : ℝ) ^ (3 * d * n) ≤ 1 := by
    calc
      (Fintype.card (CubicBondAnimal d n) : ℝ) *
          (1 / 2 : ℝ) ^ (3 * d * n) =
          ∑ _A : CubicBondAnimal d n, (1 / 2 : ℝ) ^ (3 * d * n) := by simp
      _ ≤ ∑ A : CubicBondAnimal d n,
          (half : ℝ) ^ A.edges.card * (1 - (half : ℝ)) ^ A.boundary.card :=
        Finset.sum_le_sum fun A _ ↦ hterm A
      _ ≤ 1 := hprob
  have hpowpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (3 * d * n) := by positivity
  have hcancel : (2 : ℝ) ^ (3 * d * n) * (1 / 2 : ℝ) ^ (3 * d * n) = 1 := by
    rw [← mul_pow]
    norm_num
  nlinarith

def concreteAnimalDensityDerivativeTerm {d n : ℕ}
    (A : CubicBondAnimal d n) (p : ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    ((A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
      (A.boundary.card : ℝ) * p ^ A.edges.card * (1 - p) ^ (A.boundary.card - 1))

def concreteAnimalDensityTerm {d n : ℕ} (A : CubicBondAnimal d n) (p : ℝ) : ℝ :=
  (1 / (n : ℝ)) * p ^ A.edges.card * (1 - p) ^ A.boundary.card

theorem concreteClusterDensityLevel_eq_sum_animals
    {d : ℕ} (hd : 0 < d) (n : ℕ) (p : ℝ) :
    concreteClusterDensityLevel d n p =
      ∑ A : CubicBondAnimal d n, concreteAnimalDensityTerm A p := by
  let g : CubicBondAnimal d n → ℕ × ℕ := fun A ↦ (A.edges.card, A.boundary.card)
  let f : CubicBondAnimal d n → ℝ := fun A ↦ p ^ A.edges.card * (1 - p) ^ A.boundary.card
  have hmaps : ∀ A ∈ (Finset.univ : Finset (CubicBondAnimal d n)),
      g A ∈ animalParameterPairs d n := by
    intro A _hA
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨A.edges_card_lower, A.edges_card_upper⟩,
        Finset.mem_Icc.mpr ⟨A.boundary_card_pos hd, A.boundary_card_le⟩⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps f
  rw [concreteClusterDensityLevel]
  change (1 / (n : ℝ)) * _ =
    ∑ A : CubicBondAnimal d n,
      (1 / (n : ℝ)) * p ^ A.edges.card * (1 - p) ^ A.boundary.card
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro z hz
  have hconst : ∀ A ∈ (Finset.univ.filter fun A : CubicBondAnimal d n ↦ g A = z),
      f A = p ^ z.1 * (1 - p) ^ z.2 := by
    intro A hA
    have hAz := (Finset.mem_filter.mp hA).2
    have hm := congrArg Prod.fst hAz
    have hb := congrArg Prod.snd hAz
    simp only [g] at hm hb
    simp [f, hm, hb]
  have hfiberCard : (Finset.univ.filter fun A : CubicBondAnimal d n ↦ g A = z).card =
      cubicAnimalCount d n z.1 z.2 := by
    rw [cubicAnimalCount, ← Fintype.card_subtype (fun A : CubicBondAnimal d n ↦ g A = z)]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivProp
    funext A
    apply propext
    exact Prod.ext_iff
  rw [Finset.sum_eq_card_nsmul hconst, nsmul_eq_mul, hfiberCard]

theorem concreteClusterDensityLevelDerivative_eq_sum_animals
    {d : ℕ} (hd : 0 < d) (n : ℕ) (p : ℝ) :
    concreteClusterDensityLevelDerivative d n p =
      ∑ A : CubicBondAnimal d n, concreteAnimalDensityDerivativeTerm A p := by
  let g : CubicBondAnimal d n → ℕ × ℕ := fun A ↦ (A.edges.card, A.boundary.card)
  let f : CubicBondAnimal d n → ℝ := fun A ↦
    (A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
      (A.boundary.card : ℝ) * p ^ A.edges.card * (1 - p) ^ (A.boundary.card - 1)
  have hmaps : ∀ A ∈ (Finset.univ : Finset (CubicBondAnimal d n)),
      g A ∈ animalParameterPairs d n := by
    intro A _hA
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨A.edges_card_lower, A.edges_card_upper⟩,
        Finset.mem_Icc.mpr ⟨A.boundary_card_pos hd, A.boundary_card_le⟩⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps f
  rw [concreteClusterDensityLevelDerivative]
  change (1 / (n : ℝ)) * _ = _
  simp_rw [concreteAnimalDensityDerivativeTerm, ← Finset.mul_sum]
  congr 1
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro z hz
  have hconst : ∀ A ∈ (Finset.univ.filter fun A : CubicBondAnimal d n ↦ g A = z),
      f A = (z.1 : ℝ) * p ^ (z.1 - 1) * (1 - p) ^ z.2 -
        (z.2 : ℝ) * p ^ z.1 * (1 - p) ^ (z.2 - 1) := by
    intro A hA
    have hAz := (Finset.mem_filter.mp hA).2
    have hm := congrArg Prod.fst hAz
    have hb := congrArg Prod.snd hAz
    simp only [g] at hm hb
    simp [f, hm, hb]
  have hfiberCard : (Finset.univ.filter fun A : CubicBondAnimal d n ↦ g A = z).card =
      cubicAnimalCount d n z.1 z.2 := by
    rw [cubicAnimalCount, ← Fintype.card_subtype (fun A : CubicBondAnimal d n ↦ g A = z)]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivProp
    funext A
    apply propext
    exact Prod.ext_iff
  rw [Finset.sum_eq_card_nsmul hconst, nsmul_eq_mul, hfiberCard]

/-- A concrete complex-free neighborhood of zero on which the differentiated animal series
has a geometric majorant.  The exponent is deliberately generous: the factor `3d` counts
animal choices, while `2d` controls boundary edges. -/
def clusterDensityEndpointRadius (d : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (5 * d + 2)

theorem clusterDensityEndpointRadius_pos (d : ℕ) :
    0 < clusterDensityEndpointRadius d := by
  unfold clusterDensityEndpointRadius
  positivity

theorem clusterDensityEndpointRadius_le_one (d : ℕ) :
    clusterDensityEndpointRadius d ≤ 1 := by
  unfold clusterDensityEndpointRadius
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem clusterDensityEndpoint_geometricBase_le_quarter (d : ℕ) :
    (2 : ℝ) ^ (3 * d) * (1 + clusterDensityEndpointRadius d) ^ (2 * d) *
        clusterDensityEndpointRadius d ≤ 1 / 4 := by
  have hr := clusterDensityEndpointRadius_le_one d
  have hr0 := (clusterDensityEndpointRadius_pos d).le
  have hbase : 1 + clusterDensityEndpointRadius d ≤ 2 := by linarith
  have hbase0 : 0 ≤ 1 + clusterDensityEndpointRadius d := by positivity
  calc
    (2 : ℝ) ^ (3 * d) * (1 + clusterDensityEndpointRadius d) ^ (2 * d) *
          clusterDensityEndpointRadius d ≤
        (2 : ℝ) ^ (3 * d) * 2 ^ (2 * d) * clusterDensityEndpointRadius d := by
      gcongr
    _ = 1 / 4 := by
      rw [← pow_add]
      simp only [clusterDensityEndpointRadius]
      rw [show 3 * d + 2 * d = 5 * d by omega, pow_add, ← mul_assoc, ← mul_pow]
      norm_num

theorem norm_concreteAnimalDensityDerivativeTerm_le
    {d n : ℕ} (hn : 3 ≤ n) {p : ℝ}
    (hp : ‖p‖ ≤ clusterDensityEndpointRadius d) (A : CubicBondAnimal d n) :
    ‖concreteAnimalDensityDerivativeTerm A p‖ ≤
      (3 * d : ℝ) * clusterDensityEndpointRadius d ^ (n - 2) *
        (1 + clusterDensityEndpointRadius d) ^ (2 * d * n) := by
  let R := clusterDensityEndpointRadius d
  have hR0 : 0 ≤ R := (clusterDensityEndpointRadius_pos d).le
  have hR1 : R ≤ 1 := clusterDensityEndpointRadius_le_one d
  have hq0 : 1 ≤ 1 + R := by linarith
  have hedgeLower := A.edges_card_lower
  have hboundaryUpper := A.boundary_card_le
  have hp1 : ‖p‖ ^ (A.edges.card - 1) ≤ R ^ (n - 2) := by
    calc
      ‖p‖ ^ (A.edges.card - 1) ≤ R ^ (A.edges.card - 1) := by gcongr
      _ ≤ R ^ (n - 2) :=
        pow_le_pow_of_le_one hR0 hR1 (by omega : n - 2 ≤ A.edges.card - 1)
  have hp2 : ‖p‖ ^ A.edges.card ≤ R ^ (n - 2) := by
    calc
      ‖p‖ ^ A.edges.card ≤ R ^ A.edges.card := by gcongr
      _ ≤ R ^ (n - 2) :=
        pow_le_pow_of_le_one hR0 hR1 (by omega : n - 2 ≤ A.edges.card)
  have hq : ‖1 - p‖ ≤ 1 + R := by
    calc
      ‖1 - p‖ ≤ ‖(1 : ℝ)‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ 1 + R := by simpa using add_le_add_left hp 1
  have hq1 : ‖1 - p‖ ^ A.boundary.card ≤ (1 + R) ^ (2 * d * n) := by
    calc
      ‖1 - p‖ ^ A.boundary.card ≤ (1 + R) ^ A.boundary.card := by gcongr
      _ ≤ (1 + R) ^ (2 * d * n) := pow_le_pow_right₀ hq0 A.boundary_card_le
  have hq2 : ‖1 - p‖ ^ (A.boundary.card - 1) ≤
      (1 + R) ^ (2 * d * n) := by
    calc
      ‖1 - p‖ ^ (A.boundary.card - 1) ≤ (1 + R) ^ (A.boundary.card - 1) := by
        gcongr
      _ ≤ (1 + R) ^ (2 * d * n) :=
        pow_le_pow_right₀ hq0 (by omega)
  have hn0 : (0 : ℝ) < n := by positivity
  have hm : (1 / (n : ℝ)) * A.edges.card ≤ (d : ℝ) := by
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hn0).2
    exact_mod_cast A.edges_card_upper
  have hb : (1 / (n : ℝ)) * A.boundary.card ≤ (2 * d : ℝ) := by
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hn0).2
    exact_mod_cast A.boundary_card_le
  unfold concreteAnimalDensityDerivativeTerm
  rw [norm_mul]
  have hone : ‖1 / (n : ℝ)‖ = 1 / (n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [hone]
  calc
    (1 / (n : ℝ)) *
        ‖(A.edges.card : ℝ) * p ^ (A.edges.card - 1) * (1 - p) ^ A.boundary.card -
          (A.boundary.card : ℝ) * p ^ A.edges.card *
            (1 - p) ^ (A.boundary.card - 1)‖ ≤
        (1 / (n : ℝ)) *
          (‖(A.edges.card : ℝ) * p ^ (A.edges.card - 1) *
              (1 - p) ^ A.boundary.card‖ +
            ‖(A.boundary.card : ℝ) * p ^ A.edges.card *
              (1 - p) ^ (A.boundary.card - 1)‖) := by
          gcongr
          exact norm_sub_le _ _
    _ = ((1 / (n : ℝ)) * A.edges.card) *
          (‖p‖ ^ (A.edges.card - 1) * ‖1 - p‖ ^ A.boundary.card) +
        ((1 / (n : ℝ)) * A.boundary.card) *
          (‖p‖ ^ A.edges.card * ‖1 - p‖ ^ (A.boundary.card - 1)) := by
          simp only [norm_mul, norm_pow, Real.norm_natCast]
          ring
    _ ≤ (d : ℝ) *
          (R ^ (n - 2) * (1 + R) ^ (2 * d * n)) +
        (2 * d : ℝ) *
          (R ^ (n - 2) * (1 + R) ^ (2 * d * n)) := by
          gcongr
    _ = (3 * d : ℝ) * R ^ (n - 2) * (1 + R) ^ (2 * d * n) := by ring

theorem norm_concreteClusterDensityLevelDerivative_le_endpointGeometric
    {d n : ℕ} (hd : 0 < d) (hn : 3 ≤ n) {p : ℝ}
    (hp : ‖p‖ ≤ clusterDensityEndpointRadius d) :
    ‖concreteClusterDensityLevelDerivative d n p‖ ≤
      ((3 * d : ℝ) / clusterDensityEndpointRadius d ^ 2) * (1 / 4 : ℝ) ^ n := by
  let R := clusterDensityEndpointRadius d
  let B : ℝ := (2 : ℝ) ^ (3 * d) * (1 + R) ^ (2 * d) * R
  have hR0 : 0 ≤ R := (clusterDensityEndpointRadius_pos d).le
  have hRne : R ≠ 0 := ne_of_gt (clusterDensityEndpointRadius_pos d)
  have hB0 : 0 ≤ B := by positivity
  have hB : B ≤ 1 / 4 := clusterDensityEndpoint_geometricBase_le_quarter d
  rw [concreteClusterDensityLevelDerivative_eq_sum_animals hd]
  calc
    ‖∑ A : CubicBondAnimal d n, concreteAnimalDensityDerivativeTerm A p‖ ≤
        ∑ A : CubicBondAnimal d n, ‖concreteAnimalDensityDerivativeTerm A p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _A : CubicBondAnimal d n,
        (3 * d : ℝ) * R ^ (n - 2) * (1 + R) ^ (2 * d * n) := by
      apply Finset.sum_le_sum
      intro A _hA
      exact norm_concreteAnimalDensityDerivativeTerm_le hn hp A
    _ = (Fintype.card (CubicBondAnimal d n) : ℝ) *
        ((3 * d : ℝ) * R ^ (n - 2) * (1 + R) ^ (2 * d * n)) := by simp
    _ ≤ (2 : ℝ) ^ (3 * d * n) *
        ((3 * d : ℝ) * R ^ (n - 2) * (1 + R) ^ (2 * d * n)) := by
      gcongr
      exact card_cubicBondAnimal_le_pow_two_three_d_n d n
    _ = ((3 * d : ℝ) / R ^ 2) * B ^ n := by
      dsimp [B]
      rw [show n = n - 2 + 2 by omega, pow_add, pow_mul, pow_mul]
      field_simp
      ring_nf
      rw [show 2 + (n - 2) - 2 = n - 2 by omega]
    _ ≤ ((3 * d : ℝ) / R ^ 2) * (1 / 4 : ℝ) ^ n := by
      gcongr

theorem norm_concreteAnimalDensityTerm_le
    {d n : ℕ} (hn : 1 ≤ n) {p : ℝ}
    (hp : ‖p‖ ≤ clusterDensityEndpointRadius d) (A : CubicBondAnimal d n) :
    ‖concreteAnimalDensityTerm A p‖ ≤
      clusterDensityEndpointRadius d ^ (n - 1) *
        (1 + clusterDensityEndpointRadius d) ^ (2 * d * n) := by
  let R := clusterDensityEndpointRadius d
  have hR0 : 0 ≤ R := (clusterDensityEndpointRadius_pos d).le
  have hR1 : R ≤ 1 := clusterDensityEndpointRadius_le_one d
  have hq0 : 1 ≤ 1 + R := by linarith
  have hedgeLower := A.edges_card_lower
  have hboundaryUpper := A.boundary_card_le
  have hpPow : ‖p‖ ^ A.edges.card ≤ R ^ (n - 1) := by
    calc
      ‖p‖ ^ A.edges.card ≤ R ^ A.edges.card := by gcongr
      _ ≤ R ^ (n - 1) := pow_le_pow_of_le_one hR0 hR1 A.edges_card_lower
  have hq : ‖1 - p‖ ≤ 1 + R := by
    calc
      ‖1 - p‖ ≤ ‖(1 : ℝ)‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ 1 + R := by simpa using add_le_add_left hp 1
  have hqPow : ‖1 - p‖ ^ A.boundary.card ≤ (1 + R) ^ (2 * d * n) := by
    calc
      ‖1 - p‖ ^ A.boundary.card ≤ (1 + R) ^ A.boundary.card := by gcongr
      _ ≤ (1 + R) ^ (2 * d * n) := pow_le_pow_right₀ hq0 A.boundary_card_le
  have hn0 : (0 : ℝ) < n := by positivity
  have hinv : ‖1 / (n : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (n : ℝ))]
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hncast
  unfold concreteAnimalDensityTerm
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  calc
    ‖1 / (n : ℝ)‖ * ‖p‖ ^ A.edges.card * ‖1 - p‖ ^ A.boundary.card ≤
        1 * R ^ (n - 1) * (1 + R) ^ (2 * d * n) := by gcongr
    _ = R ^ (n - 1) * (1 + R) ^ (2 * d * n) := by ring

theorem norm_concreteClusterDensityLevel_le_endpointGeometric
    {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) {p : ℝ}
    (hp : ‖p‖ ≤ clusterDensityEndpointRadius d) :
    ‖concreteClusterDensityLevel d n p‖ ≤
      (1 / clusterDensityEndpointRadius d) * (1 / 4 : ℝ) ^ n := by
  let R := clusterDensityEndpointRadius d
  let B : ℝ := (2 : ℝ) ^ (3 * d) * (1 + R) ^ (2 * d) * R
  have hR0 : 0 ≤ R := (clusterDensityEndpointRadius_pos d).le
  have hRne : R ≠ 0 := ne_of_gt (clusterDensityEndpointRadius_pos d)
  have hB0 : 0 ≤ B := by positivity
  have hB : B ≤ 1 / 4 := clusterDensityEndpoint_geometricBase_le_quarter d
  rw [concreteClusterDensityLevel_eq_sum_animals hd]
  calc
    ‖∑ A : CubicBondAnimal d n, concreteAnimalDensityTerm A p‖ ≤
        ∑ A : CubicBondAnimal d n, ‖concreteAnimalDensityTerm A p‖ := norm_sum_le _ _
    _ ≤ ∑ _A : CubicBondAnimal d n,
        R ^ (n - 1) * (1 + R) ^ (2 * d * n) := by
      apply Finset.sum_le_sum
      intro A _hA
      exact norm_concreteAnimalDensityTerm_le hn hp A
    _ = (Fintype.card (CubicBondAnimal d n) : ℝ) *
        (R ^ (n - 1) * (1 + R) ^ (2 * d * n)) := by simp
    _ ≤ (2 : ℝ) ^ (3 * d * n) *
        (R ^ (n - 1) * (1 + R) ^ (2 * d * n)) := by
      gcongr
      exact card_cubicBondAnimal_le_pow_two_three_d_n d n
    _ = (1 / R) * B ^ n := by
      dsimp [B]
      rw [show n = n - 1 + 1 by omega, pow_add, pow_mul, pow_mul]
      field_simp
      ring_nf
      rw [show 1 + (n - 1) - 1 = n - 1 by omega]
    _ ≤ (1 / R) * (1 / 4 : ℝ) ^ n := by
      gcongr

theorem summable_concreteClusterDensityLevel_endpoint
    {d : ℕ} (hd : 0 < d) {p : ℝ}
    (hp : ‖p‖ ≤ clusterDensityEndpointRadius d) :
    Summable fun n : ℕ ↦ concreteClusterDensityLevel d n p := by
  let C : ℝ := 1 / clusterDensityEndpointRadius d
  have hgeom : Summable fun n : ℕ ↦ (1 / 4 : ℝ) ^ n := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  apply (hgeom.mul_left C).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact norm_concreteClusterDensityLevel_le_endpointGeometric hd hn hp

theorem summable_concreteClusterDensityLevelDerivative_endpoint
    {d : ℕ} (hd : 0 < d) {p : ℝ}
    (hp : ‖p‖ ≤ clusterDensityEndpointRadius d) :
    Summable fun n : ℕ ↦ concreteClusterDensityLevelDerivative d n p := by
  let C : ℝ := (3 * d : ℝ) / clusterDensityEndpointRadius d ^ 2
  have hgeom : Summable fun n : ℕ ↦ (1 / 4 : ℝ) ^ n := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  apply (hgeom.mul_left C).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact norm_concreteClusterDensityLevelDerivative_le_endpointGeometric hd hn hp

theorem concreteClusterDensityDerivativePartialSum_tendstoUniformlyOn_endpoint
    {d : ℕ} (hd : 0 < d) :
    TendstoUniformlyOn (concreteClusterDensityDerivativePartialSum d)
      (concreteClusterDensityDerivativeSeries d) atTop
      (Icc (-clusterDensityEndpointRadius d) (clusterDensityEndpointRadius d)) := by
  let C : ℝ := (3 * d : ℝ) / clusterDensityEndpointRadius d ^ 2
  have hgeom : Summable fun n : ℕ ↦ (1 / 4 : ℝ) ^ n := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  apply tendstoUniformlyOn_tsum_nat_eventually (hgeom.mul_left C)
  filter_upwards [eventually_ge_atTop 3] with n hn p hp
  apply norm_concreteClusterDensityLevelDerivative_le_endpointGeometric hd hn
  rw [Real.norm_eq_abs]
  exact abs_le.mpr hp

theorem concreteClusterDensityDerivativeSeries_continuousOn_endpointNeighborhood
    {d : ℕ} (hd : 0 < d) :
    ContinuousOn (concreteClusterDensityDerivativeSeries d)
      (Icc (-clusterDensityEndpointRadius d) (clusterDensityEndpointRadius d)) := by
  exact (concreteClusterDensityDerivativePartialSum_tendstoUniformlyOn_endpoint hd).continuousOn
    ((Filter.Eventually.of_forall fun N ↦
      (concreteClusterDensityDerivativePartialSum_continuous d N).continuousOn).frequently)

theorem concreteClusterDensitySeries_hasDerivAt_endpointNeighborhood
    {d : ℕ} (hd : 0 < d) {p : ℝ}
    (hp : p ∈ Ioo (-clusterDensityEndpointRadius d) (clusterDensityEndpointRadius d)) :
    HasDerivAt (concreteClusterDensitySeries d)
      (concreteClusterDensityDerivativeSeries d p) p := by
  have hderiv : TendstoUniformlyOn
      (concreteClusterDensityDerivativePartialSum d)
      (concreteClusterDensityDerivativeSeries d) atTop
      (Ioo (-clusterDensityEndpointRadius d) (clusterDensityEndpointRadius d)) :=
    (concreteClusterDensityDerivativePartialSum_tendstoUniformlyOn_endpoint hd).mono
      Ioo_subset_Icc_self
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hderiv
  · filter_upwards with N y _hy
    exact concreteClusterDensityPartialSum_hasDerivAt d N y
  · intro y hy
    have hyNorm : ‖y‖ ≤ clusterDensityEndpointRadius d := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    have hsum := summable_concreteClusterDensityLevel_endpoint hd hyNorm
    simpa only [concreteClusterDensityPartialSum, concreteClusterDensitySeries] using
      hsum.hasSum.tendsto_sum_nat
  · exact hp

theorem concreteClusterDensitySeries_hasDerivWithinAt_one
    {d : ℕ} (hd : 2 ≤ d) :
    HasDerivWithinAt (concreteClusterDensitySeries d) 0 (Icc (0 : ℝ) 1) 1 := by
  rw [hasDerivWithinAt_iff_tendsto]
  simp only [smul_zero, sub_zero]
  have hnonneg : ∀ᶠ x : ℝ in 𝓝[Icc (0 : ℝ) 1] 1,
      0 ≤ ‖x - 1‖⁻¹ * ‖concreteClusterDensitySeries d x -
        concreteClusterDensitySeries d 1‖ :=
    Filter.Eventually.of_forall fun _ ↦ mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (norm_nonneg _)
  have hle : ∀ᶠ x : ℝ in 𝓝[Icc (0 : ℝ) 1] 1,
      ‖x - 1‖⁻¹ * ‖concreteClusterDensitySeries d x -
          concreteClusterDensitySeries d 1‖ ≤ (6 * d : ℝ) * (1 - x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hdiff := norm_concreteClusterDensitySeries_sub_le hd (r := x) (x := x) (y := 1)
      hx.1 ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩
    rw [norm_sub_rev] at hdiff
    by_cases hxeq : x = 1
    · simp [hxeq]
    · have hnorm : ‖x - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxeq)
      calc
        ‖x - 1‖⁻¹ * ‖concreteClusterDensitySeries d x -
            concreteClusterDensitySeries d 1‖ ≤
            ‖x - 1‖⁻¹ * ((6 * d * (1 - x)) * ‖1 - x‖) := by
          gcongr
        _ = 6 * d * (1 - x) := by
          rw [norm_sub_rev (1 : ℝ) x]
          field_simp
  have ht : Tendsto (fun x : ℝ ↦ (6 * d : ℝ) * (1 - x))
      (𝓝 (1 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds.sub tendsto_id).const_mul (6 * d : ℝ) using 1
    all_goals ring_nf
  exact squeeze_zero' hnonneg hle (ht.mono_left inf_le_left)

theorem norm_concreteClusterDensityDerivativeSeries_le_one_sub
    {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hpHalf : 1 / 2 < p) (hp1 : p < 1) :
    ‖concreteClusterDensityDerivativeSeries d p‖ ≤ (12 * d : ℝ) * (1 - p) := by
  let r := 2 * p - 1
  let C := (12 * d : ℝ) * (1 - p)
  have hr0 : 0 ≤ r := by dsimp only [r]; linarith
  have hrp : r < p := by dsimp only [r]; linarith
  have hp_mem : p ∈ Icc r 1 := ⟨hrp.le, hp1.le⟩
  have hlocal : ∀ᶠ y in 𝓝 p,
      ‖concreteClusterDensitySeries d y - concreteClusterDensitySeries d p‖ ≤
        C * ‖y - p‖ := by
    filter_upwards [Icc_mem_nhds hrp hp1] with y hy
    have h := norm_concreteClusterDensitySeries_sub_le hd hr0 hp_mem hy
    convert h using 1
    all_goals dsimp only [C, r]
    all_goals ring_nf
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hderiv := norm_deriv_le_of_lip' hC0 hlocal
  have hhas := concreteClusterDensitySeries_hasDerivAt (by omega : 0 < d) (by linarith) hp1
  rw [hhas.deriv] at hderiv
  exact hderiv

/-- The derivative used to stitch the two endpoint arguments to the interior animal series. -/
def concreteClusterDensityClosedDerivative (d : ℕ) (p : ℝ) : ℝ :=
  if p = 1 then 0 else concreteClusterDensityDerivativeSeries d p

theorem derivWithin_concreteClusterDensitySeries_eq_closedDerivative
    {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    derivWithin (concreteClusterDensitySeries d) (Icc (0 : ℝ) 1) p =
      concreteClusterDensityClosedDerivative d p := by
  by_cases hp1 : p = 1
  · subst p
    rw [(concreteClusterDensitySeries_hasDerivWithinAt_one hd).derivWithin
      (uniqueDiffOn_Icc_zero_one 1 ⟨zero_le_one, le_rfl⟩)]
    simp [concreteClusterDensityClosedDerivative]
  · have hpLt : p < 1 := lt_of_le_of_ne hp.2 hp1
    have hhas : HasDerivAt (concreteClusterDensitySeries d)
        (concreteClusterDensityDerivativeSeries d p) p := by
      by_cases hp0 : p = 0
      · subst p
        apply concreteClusterDensitySeries_hasDerivAt_endpointNeighborhood (by omega : 0 < d)
        exact ⟨neg_lt_zero.mpr (clusterDensityEndpointRadius_pos d),
          clusterDensityEndpointRadius_pos d⟩
      · exact concreteClusterDensitySeries_hasDerivAt (by omega : 0 < d)
          (lt_of_le_of_ne hp.1 (Ne.symm hp0)) hpLt
    rw [concreteClusterDensityClosedDerivative, if_neg hp1]
    exact hhas.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc_zero_one p hp)

theorem concreteClusterDensityClosedDerivative_continuousWithinAt_one
    {d : ℕ} (hd : 2 ≤ d) :
    ContinuousWithinAt (concreteClusterDensityClosedDerivative d) (Icc (0 : ℝ) 1) 1 := by
  rw [ContinuousWithinAt]
  have hvalue : concreteClusterDensityClosedDerivative d 1 = 0 := by
    simp [concreteClusterDensityClosedDerivative]
  rw [hvalue]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hnonneg : ∀ᶠ x : ℝ in 𝓝[Icc (0 : ℝ) 1] 1,
      0 ≤ ‖concreteClusterDensityClosedDerivative d x‖ :=
    Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  have hle : ∀ᶠ x : ℝ in 𝓝[Icc (0 : ℝ) 1] 1,
      ‖concreteClusterDensityClosedDerivative d x‖ ≤ (12 * d : ℝ) * (1 - x) := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono inf_le_left
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with x hx hxHalf
    by_cases hxeq : x = 1
    · simp [concreteClusterDensityClosedDerivative, hxeq]
    · have hx1 : x < 1 := lt_of_le_of_ne hx.2 hxeq
      simpa [concreteClusterDensityClosedDerivative, hxeq] using
        norm_concreteClusterDensityDerivativeSeries_le_one_sub hd hxHalf hx1
  have ht : Tendsto (fun x : ℝ ↦ (12 * d : ℝ) * (1 - x))
      (𝓝 (1 : ℝ)) (𝓝 0) := by
    convert (tendsto_const_nhds.sub tendsto_id).const_mul (12 * d : ℝ) using 1
    all_goals ring_nf
  exact squeeze_zero' hnonneg hle (ht.mono_left inf_le_left)

theorem concreteClusterDensityClosedDerivative_continuousOn
    {d : ℕ} (hd : 2 ≤ d) :
    ContinuousOn (concreteClusterDensityClosedDerivative d) (Icc (0 : ℝ) 1) := by
  intro p hp
  by_cases hp1 : p = 1
  · subst p
    exact concreteClusterDensityClosedDerivative_continuousWithinAt_one hd
  · have hpLt : p < 1 := lt_of_le_of_ne hp.2 hp1
    have hseries : ContinuousWithinAt (concreteClusterDensityDerivativeSeries d)
        (Icc (0 : ℝ) 1) p := by
      by_cases hp0 : p = 0
      · subst p
        have hneg : -clusterDensityEndpointRadius d < (0 : ℝ) :=
          neg_lt_zero.mpr (clusterDensityEndpointRadius_pos d)
        have hpos : (0 : ℝ) < clusterDensityEndpointRadius d :=
          clusterDensityEndpointRadius_pos d
        exact ((concreteClusterDensityDerivativeSeries_continuousOn_endpointNeighborhood
          (by omega : 0 < d)).continuousAt (Icc_mem_nhds hneg hpos)).continuousWithinAt
      · have hpPos : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
        exact (((concreteClusterDensityDerivativeSeries_continuousOn_Ioo (by omega : 0 < d))
          p ⟨hpPos, hpLt⟩).continuousAt
            (isOpen_Ioo.mem_nhds ⟨hpPos, hpLt⟩)).continuousWithinAt
    apply hseries.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hpLt)] with x hx
      simp [concreteClusterDensityClosedDerivative, ne_of_lt hx]
    · simp [concreteClusterDensityClosedDerivative, hp1]

/-- **Grimmett, Theorem 4.31 (closed-interval, unconditional form).**

For `d ≥ 2`, the concrete rooted-animal expansion of the open-cluster density is continuously
differentiable on the whole physical interval `[0,1]`.  The proof combines the animal-series
majorant near zero, the interior large-deviation argument, and the periodic-volume square-detour
estimate near one; it has no coefficient, differentiability, or convergence hypotheses. -/
theorem concreteClusterDensitySeries_contDiffOn_unitInterval
    {d : ℕ} (hd : 2 ≤ d) :
    ContDiffOn ℝ 1 (concreteClusterDensitySeries d) (Icc (0 : ℝ) 1) := by
  apply (contDiffOn_one_iff_derivWithin uniqueDiffOn_Icc_zero_one).2
  constructor
  · intro p hp
    by_cases hp1 : p = 1
    · subst p
      exact (concreteClusterDensitySeries_hasDerivWithinAt_one hd).differentiableWithinAt
    · have hpLt : p < 1 := lt_of_le_of_ne hp.2 hp1
      by_cases hp0 : p = 0
      · subst p
        exact (concreteClusterDensitySeries_hasDerivAt_endpointNeighborhood
          (by omega : 0 < d) ⟨neg_lt_zero.mpr (clusterDensityEndpointRadius_pos d),
            clusterDensityEndpointRadius_pos d⟩).differentiableAt.differentiableWithinAt
      · exact (concreteClusterDensitySeries_hasDerivAt (by omega : 0 < d)
          (lt_of_le_of_ne hp.1 (Ne.symm hp0)) hpLt).differentiableAt.differentiableWithinAt
  · exact (concreteClusterDensityClosedDerivative_continuousOn hd).congr fun p hp ↦
      derivWithin_concreteClusterDensitySeries_eq_closedDerivative hd hp

theorem torusClusterDensitySeries_tendsto_openClustersPerVertex
    (d : ℕ) (p : I) :
    Tendsto (fun j : ℕ ↦ torusClusterDensitySeries d (j + 2) (by omega) p)
      atTop (nhds (openClustersPerVertex d p)) :=
  torusClusterDensitySeries_tendsto_openClustersPerVertex_aux d p

end

end Percolation
