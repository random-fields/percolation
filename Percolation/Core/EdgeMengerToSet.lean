import Percolation.Core.EdgeMenger
import Mathlib.Tactic

/-!
# Arbitrary finite edge Menger to terminal sets

This file supplies the terminal-set adapter needed by the planar crossing arguments in
Grimmett Lemma 11.22 and Theorem 7.68.  A common sink is joined to each target through `k`
private two-edge channels.  Consequently deleting fewer than `k` auxiliary edges cannot create
an artificial terminal bottleneck.
-/

namespace Percolation

namespace EdgeMenger

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- Original vertices, `k` private channels per target, and a common sink. -/
abbrev TargetAuxVertex (T : Finset V) (k : ℕ) :=
  Sum V (Sum ({v : V // v ∈ T} × Fin k) Unit)

def targetAuxOriginal {T : Finset V} {k : ℕ} (v : V) : TargetAuxVertex T k :=
  Sum.inl v

def targetAuxChannel {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) (i : Fin k) : TargetAuxVertex T k :=
  Sum.inr (Sum.inl (t, i))

def targetAuxSink {T : Finset V} {k : ℕ} : TargetAuxVertex T k :=
  Sum.inr (Sum.inr ())

def targetAuxRel (G : SimpleGraph V) (T : Finset V) (k : ℕ) :
    TargetAuxVertex T k → TargetAuxVertex T k → Prop
  | Sum.inl u, Sum.inl v => G.Adj u v
  | Sum.inl u, Sum.inr (Sum.inl c) => u = c.1.1
  | Sum.inr (Sum.inl _c), Sum.inr (Sum.inr _) => True
  | _, _ => False

def targetAuxGraph (G : SimpleGraph V) (T : Finset V) (k : ℕ) :
    SimpleGraph (TargetAuxVertex T k) :=
  SimpleGraph.fromRel (targetAuxRel G T k)

omit [DecidableEq V] in
theorem targetAuxGraph_adj_original {T : Finset V} {k : ℕ} {u v : V}
    (h : G.Adj u v) :
    (targetAuxGraph G T k).Adj (targetAuxOriginal u) (targetAuxOriginal v) := by
  rw [targetAuxGraph, SimpleGraph.fromRel_adj]
  exact ⟨fun huv ↦ h.ne (Sum.inl.inj huv), Or.inl h⟩

omit [DecidableEq V] in
theorem targetAuxGraph_adj_channel {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) (i : Fin k) :
    (targetAuxGraph G T k).Adj (targetAuxOriginal t.1) (targetAuxChannel t i) := by
  rw [targetAuxGraph, SimpleGraph.fromRel_adj]
  simp [targetAuxRel, targetAuxOriginal, targetAuxChannel]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_sink {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) (i : Fin k) :
    (targetAuxGraph G T k).Adj (targetAuxChannel t i) targetAuxSink := by
  rw [targetAuxGraph, SimpleGraph.fromRel_adj]
  simp [targetAuxRel, targetAuxChannel, targetAuxSink]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_original_iff {T : Finset V} {k : ℕ} {u : V}
    {v : TargetAuxVertex T k} :
    (targetAuxGraph G T k).Adj (targetAuxOriginal u) v ↔
      (∃ w, v = targetAuxOriginal w ∧ G.Adj u w) ∨
      (∃ c : {v : V // v ∈ T} × Fin k,
        v = targetAuxChannel c.1 c.2 ∧ u = c.1.1) := by
  cases v with
  | inl w =>
      rw [targetAuxGraph, SimpleGraph.fromRel_adj]
      simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, G.adj_comm]
      exact fun h ↦ h.ne
  | inr v =>
      cases v with
      | inl c =>
          rcases c with ⟨t, i⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel]
      | inr sinkUnit =>
          rcases sinkUnit with ⟨⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_sink_iff {T : Finset V} {k : ℕ}
    {v : TargetAuxVertex T k} :
    (targetAuxGraph G T k).Adj v targetAuxSink ↔
      ∃ c : {v : V // v ∈ T} × Fin k, v = targetAuxChannel c.1 c.2 := by
  cases v with
  | inl u =>
      rw [targetAuxGraph, SimpleGraph.fromRel_adj]
      simp [targetAuxRel, targetAuxChannel, targetAuxSink]
  | inr v =>
      cases v with
      | inl c =>
          rcases c with ⟨t, i⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxChannel, targetAuxSink]
      | inr sinkUnit =>
          rcases sinkUnit with ⟨⟩
          simp [targetAuxSink, targetAuxChannel]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_channel_iff {T : Finset V} {k : ℕ}
    {c : {v : V // v ∈ T} × Fin k} {v : TargetAuxVertex T k} :
    (targetAuxGraph G T k).Adj v (targetAuxChannel c.1 c.2) ↔
      v = targetAuxOriginal c.1.1 ∨ v = targetAuxSink := by
  cases v with
  | inl u =>
      rw [targetAuxGraph, SimpleGraph.fromRel_adj]
      simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, targetAuxSink]
  | inr v =>
      cases v with
      | inl c' =>
          rcases c with ⟨t, i⟩
          rcases c' with ⟨t', j⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, targetAuxSink]
      | inr sinkUnit =>
          rcases sinkUnit with ⟨⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, targetAuxSink]

def targetAuxOriginalHom (T : Finset V) (k : ℕ) : G →g targetAuxGraph G T k where
  toFun := targetAuxOriginal
  map_rel' := targetAuxGraph_adj_original

def walkToTargetAux {T : Finset V} {k : ℕ} {u t : V} (p : G.Walk u t)
    (ht : t ∈ T) (i : Fin k) :
    (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink :=
  ((p.map (targetAuxOriginalHom T k)).concat
    (targetAuxGraph_adj_channel ⟨t, ht⟩ i)).concat
      (targetAuxGraph_adj_sink ⟨t, ht⟩ i)

omit [DecidableEq V] in
theorem walkToTargetAux_edges {T : Finset V} {k : ℕ} {u t : V}
    (p : G.Walk u t) (ht : t ∈ T) (i : Fin k) :
    (walkToTargetAux p ht i).edges =
      p.edges.map (Sym2.map targetAuxOriginal) ++
        [s(targetAuxOriginal t, targetAuxChannel ⟨t, ht⟩ i),
          s(targetAuxChannel ⟨t, ht⟩ i, targetAuxSink)] := by
  unfold walkToTargetAux
  change ((((p.map (targetAuxOriginalHom T k)).concat
    (targetAuxGraph_adj_channel ⟨t, ht⟩ i)).concat
      (targetAuxGraph_adj_sink ⟨t, ht⟩ i)).edges) = _
  rw [SimpleGraph.Walk.edges_concat, SimpleGraph.Walk.edges_concat,
    SimpleGraph.Walk.edges_map]
  simp [List.concat_eq_append, targetAuxOriginalHom]

omit [DecidableEq V] in
theorem targetAuxOriginal_injective {T : Finset V} {k : ℕ} :
    Function.Injective (targetAuxOriginal (T := T) (k := k)) :=
  Sum.inl_injective

omit [DecidableEq V] in
theorem targetAuxChannel_injective_fixed {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) :
    Function.Injective (targetAuxChannel (k := k) t) := by
  intro i j h
  exact congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj h))

omit [DecidableEq V] in
theorem targetAux_channelEntry_injective {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) :
    Function.Injective
      (fun i : Fin k ↦ s(targetAuxOriginal t.1, targetAuxChannel t i)) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with hsame | hswap
  · exact targetAuxChannel_injective_fixed t hsame.2
  · exact (Sum.inl_ne_inr hswap.1).elim

omit [DecidableEq V] in
theorem targetAux_channelExit_injective {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) :
    Function.Injective
      (fun i : Fin k ↦ s(targetAuxChannel t i, targetAuxSink)) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with hsame | hswap
  · exact targetAuxChannel_injective_fixed t hsame.1
  · exact (Sum.inl_ne_inr (Sum.inr.inj hswap.1)).elim

omit [DecidableEq V] in
theorem targetAux_channelEntry_ne_channelExit {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) (i j : Fin k) :
    s(targetAuxOriginal t.1, targetAuxChannel t i) ≠
      s(targetAuxChannel t j, targetAuxSink) := by
  intro h
  rcases Sym2.eq_iff.mp h with hsame | hswap
  · exact Sum.inl_ne_inr hsame.1
  · exact Sum.inl_ne_inr hswap.1

omit [DecidableEq V] in
/-- Fewer than `k` deleted auxiliary edges leave at least one complete private channel of a
fixed terminal. -/
theorem exists_targetAux_channel_avoiding {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) (s : Set (Sym2 (TargetAuxVertex T k)))
    (hs : s.encard < (k : ℕ)) :
    ∃ i : Fin k,
      s(targetAuxOriginal t.1, targetAuxChannel t i) ∉ s ∧
        s(targetAuxChannel t i, targetAuxSink) ∉ s := by
  classical
  have hsFinite : s.Finite := Set.finite_of_encard_le_coe hs.le
  letI : Fintype s := hsFinite.fintype
  by_contra hno
  push Not at hno
  let blocked : Fin k → Sym2 (TargetAuxVertex T k) := fun i ↦
    if s(targetAuxOriginal t.1, targetAuxChannel t i) ∈ s then
      s(targetAuxOriginal t.1, targetAuxChannel t i)
    else s(targetAuxChannel t i, targetAuxSink)
  have hblockedMem (i : Fin k) : blocked i ∈ s := by
    by_cases hi : s(targetAuxOriginal t.1, targetAuxChannel t i) ∈ s
    · simp [blocked, hi]
    · simp [blocked, hi, hno i hi]
  have hblockedInj : Function.Injective blocked := by
    intro i j hij
    by_cases hi : s(targetAuxOriginal t.1, targetAuxChannel t i) ∈ s <;>
      by_cases hj : s(targetAuxOriginal t.1, targetAuxChannel t j) ∈ s
    · exact targetAux_channelEntry_injective t (by simpa [blocked, hi, hj] using hij)
    · exact (targetAux_channelEntry_ne_channelExit t i j
        (by simpa [blocked, hi, hj] using hij)).elim
    · exact (targetAux_channelEntry_ne_channelExit t j i
        (by simpa [blocked, hi, hj] using hij.symm)).elim
    · exact targetAux_channelExit_injective t (by simpa [blocked, hi, hj] using hij)
  let f : Fin k → s := fun i ↦ ⟨blocked i, hblockedMem i⟩
  have hk : k ≤ Fintype.card s := by
    simpa using Fintype.card_le_of_injective f (by
      intro i j hij
      exact hblockedInj (Subtype.ext_iff.mp hij))
  have hk' : (k : ℕ∞) ≤ (Fintype.card s : ℕ∞) := ENat.coe_le_coe.mpr hk
  rw [Set.coe_fintypeCard] at hk'
  exact (not_le_of_gt hs) hk'

omit [DecidableEq V] in
theorem targetAux_channelEntry_ne_map_original {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) (i : Fin k) (e : Sym2 V) :
    s(targetAuxOriginal t.1, targetAuxChannel t i) ≠
      Sym2.map targetAuxOriginal e := by
  intro h
  have hmem : targetAuxChannel t i ∈ Sym2.map targetAuxOriginal e := by
    rw [← h]
    simp
  rw [Sym2.mem_map] at hmem
  obtain ⟨v, _hv, hv⟩ := hmem
  exact Sum.inl_ne_inr hv

omit [DecidableEq V] in
theorem targetAux_channelExit_ne_map_original {T : Finset V} {k : ℕ}
    (t : {v : V // v ∈ T}) (i : Fin k) (e : Sym2 V) :
    s(targetAuxChannel t i, targetAuxSink) ≠
      Sym2.map targetAuxOriginal e := by
  intro h
  have hmem : (targetAuxSink : TargetAuxVertex T k) ∈
      Sym2.map targetAuxOriginal e := by
    rw [← h]
    simp
  rw [Sym2.mem_map] at hmem
  obtain ⟨v, _hv, hv⟩ := hmem
  exact Sum.inl_ne_inr hv

/-- Cut-survival from one source to a finite target set, expressed by ambient walks avoiding
the deleted edges.  This form is convenient for terminal gadgets and is equivalent to the
usual deleted-graph reachability formulation. -/
def IsEdgeReachableToFinset (G : SimpleGraph V) (k : ℕ) (u : V)
    (T : Finset V) : Prop :=
  ∀ s : Set (Sym2 V), s.encard < (k : ℕ) →
    ∃ t ∈ T, ∃ p : G.Walk u t, ∀ e ∈ p.edges, e ∉ s

omit [DecidableEq V] in
theorem isEdgeReachableToFinset_zero (G : SimpleGraph V) (u : V) (T : Finset V) :
    IsEdgeReachableToFinset G 0 u T := by
  intro s hs
  simp at hs

omit [DecidableEq V] in
/-- The private-channel auxiliary graph has ordinary `k`-edge reachability whenever the
original graph survives every cut of size less than `k` to the target set. -/
theorem targetAux_isEdgeReachable {T : Finset V} {u : V} {k : ℕ}
    (hreach : IsEdgeReachableToFinset G k u T) :
    (targetAuxGraph G T k).IsEdgeReachable k (targetAuxOriginal u) targetAuxSink := by
  classical
  intro s hs
  let f : Sym2 V → Sym2 (TargetAuxVertex T k) := Sym2.map targetAuxOriginal
  let originalDeleted : Set (Sym2 V) := f ⁻¹' s
  have hf : Function.Injective f := by
    exact Sym2.map.injective targetAuxOriginal_injective
  have hdeletedCard : originalDeleted.encard ≤ s.encard := by
    calc
      originalDeleted.encard = (f '' originalDeleted).encard :=
        (hf.encard_image originalDeleted).symm
      _ ≤ s.encard := Set.encard_mono (Set.image_preimage_subset f s)
  have hdeletedLt : originalDeleted.encard < (k : ℕ) := hdeletedCard.trans_lt hs
  obtain ⟨t, ht, p, hp⟩ := hreach originalDeleted hdeletedLt
  obtain ⟨i, hiEntry, hiExit⟩ :=
    exists_targetAux_channel_avoiding (⟨t, ht⟩ : {v : V // v ∈ T}) s hs
  let q := walkToTargetAux p ht i
  refine ⟨q.toDeleteEdges s ?_⟩
  intro e he
  rw [walkToTargetAux_edges p ht i] at he
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with he | he | he
  · obtain ⟨e₀, he₀, rfl⟩ := he
    exact hp e₀ he₀
  · simpa only [he] using hiEntry
  · simpa only [he] using hiExit

omit [DecidableEq V] in
theorem exists_target_original_mem_support {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) : ∃ t ∈ T, targetAuxOriginal t ∈ p.support := by
  have hnil : ¬p.Nil := by
    intro h
    exact Sum.inl_ne_inr h.eq
  have hsink : targetAuxSink ∉ p.dropLast.support := by
    have hnodup : (p.dropLast.support ++ [targetAuxSink]).Nodup := by
      rw [p.support_dropLast_concat hnil]
      exact hp.support_nodup
    have h := (List.nodup_append.mp hnodup).2.2
    exact fun hmem ↦ h targetAuxSink hmem targetAuxSink (by simp) rfl
  have hadj := p.adj_penultimate hnil
  obtain ⟨c, hc⟩ := targetAuxGraph_adj_sink_iff.mp hadj
  let p₁ : (targetAuxGraph G T k).Walk (targetAuxOriginal u)
      (targetAuxChannel c.1 c.2) := p.dropLast.copy rfl hc
  have hp₁nil : ¬p₁.Nil := by
    intro h
    have heq := h.eq
    change targetAuxOriginal u = targetAuxChannel c.1 c.2 at heq
    exact Sum.inl_ne_inr heq
  have hadj₁ := p₁.adj_penultimate hp₁nil
  rcases targetAuxGraph_adj_channel_iff.mp hadj₁ with horig | hsinkpen
  · refine ⟨c.1.1, c.1.2, ?_⟩
    have hmem : p₁.penultimate ∈ p₁.support :=
      List.mem_of_mem_dropLast (p₁.penultimate_mem_dropLast_support hp₁nil)
    have hmemDrop : targetAuxOriginal c.1.1 ∈ p.dropLast.support := by
      simpa [p₁, horig] using hmem
    exact (SimpleGraph.Walk.isSubwalk_take p (p.length - 1)).support_subset hmemDrop
  · have hmem : p₁.penultimate ∈ p₁.support :=
      List.mem_of_mem_dropLast (p₁.penultimate_mem_dropLast_support hp₁nil)
    have : targetAuxSink ∈ p.dropLast.support := by
      simpa [p₁, hsinkpen] using hmem
    exact (hsink this).elim

omit [DecidableEq V] in
theorem firstTarget_exists {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) :
    ∃ j : ℕ, j ≤ p.length ∧
      ∃ t : {v : V // v ∈ T}, p.getVert j = targetAuxOriginal t.1 := by
  obtain ⟨t, ht, hmem⟩ := exists_target_original_mem_support p hp
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨j, hjt, hj⟩ := hmem
  exact ⟨j, hj, ⟨t, ht⟩, hjt⟩

noncomputable def firstTargetIndex {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) : ℕ :=
  Nat.find (firstTarget_exists p hp)

theorem firstTargetIndex_spec {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) :
    firstTargetIndex p hp ≤ p.length ∧
      ∃ t : {v : V // v ∈ T},
        p.getVert (firstTargetIndex p hp) = targetAuxOriginal t.1 :=
  Nat.find_spec (firstTarget_exists p hp)

theorem getVert_eq_original_of_le_firstTargetIndex {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) {j : ℕ} (hj : j ≤ firstTargetIndex p hp) :
    ∃ v : V, p.getVert j = targetAuxOriginal v := by
  induction j with
  | zero => exact ⟨u, by simp⟩
  | succ j ih =>
      have hjlt : j < firstTargetIndex p hp := by omega
      have hjlen : j < p.length := hjlt.trans_le (firstTargetIndex_spec p hp).1
      obtain ⟨v, hv⟩ := ih (by omega)
      have hadj := p.adj_getVert_succ hjlen
      rw [hv] at hadj
      rcases targetAuxGraph_adj_original_iff.mp hadj with h | h
      · obtain ⟨w, hw, _hvw⟩ := h
        exact ⟨w, hw⟩
      · obtain ⟨c, hc, hvc⟩ := h
        exfalso
        apply Nat.find_min (firstTarget_exists p hp) hjlt
        refine ⟨hjlen.le, c.1, ?_⟩
        rw [hv, hvc]

theorem firstTargetPrefix_support_original {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) :
    ∀ a ∈ (p.take (firstTargetIndex p hp)).support,
      ∃ v : V, a = targetAuxOriginal v := by
  intro a ha
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at ha
  obtain ⟨j, hja, hj⟩ := ha
  have hk := (firstTargetIndex_spec p hp).1
  have hlength : (p.take (firstTargetIndex p hp)).length = firstTargetIndex p hp := by
    simp [Nat.min_eq_left hk]
  have hjk : j ≤ firstTargetIndex p hp := by omega
  obtain ⟨v, hv⟩ := getVert_eq_original_of_le_firstTargetIndex p hp hjk
  refine ⟨v, ?_⟩
  rw [← hja]
  simpa [Nat.min_eq_right hjk] using hv

def targetAuxOriginalSet (T : Finset V) (k : ℕ) : Set (TargetAuxVertex T k) :=
  Set.range targetAuxOriginal

noncomputable def targetAuxOriginalGet {T : Finset V} {k : ℕ}
    (a : targetAuxOriginalSet T k) : V :=
  Classical.choose a.2

omit [DecidableEq V] in
theorem targetAuxOriginalGet_spec {T : Finset V} {k : ℕ}
    (a : targetAuxOriginalSet T k) :
    targetAuxOriginal (targetAuxOriginalGet a) = a.1 :=
  Classical.choose_spec a.2

omit [DecidableEq V] in
@[simp]
theorem targetAuxOriginalGet_mk {T : Finset V} {k : ℕ} (v : V) :
    targetAuxOriginalGet
      (⟨targetAuxOriginal v, ⟨v, rfl⟩⟩ : targetAuxOriginalSet T k) = v := by
  apply Sum.inl.inj
  exact targetAuxOriginalGet_spec _

noncomputable def targetAuxOriginalSetHom (T : Finset V) (k : ℕ) :
    (targetAuxGraph G T k).induce (targetAuxOriginalSet T k) →g G where
  toFun := targetAuxOriginalGet
  map_rel' := by
    intro a b hab
    have hab' : (targetAuxGraph G T k).Adj a.1 b.1 := SimpleGraph.induce_adj.mp hab
    rw [← targetAuxOriginalGet_spec a, ← targetAuxOriginalGet_spec b] at hab'
    rcases targetAuxGraph_adj_original_iff.mp hab' with h | h
    · obtain ⟨w, hw, hadj⟩ := h
      have hw' : w = targetAuxOriginalGet b := Sum.inl.inj hw.symm
      simpa [hw'] using hadj
    · obtain ⟨c, hc, _⟩ := h
      exact (Sum.inl_ne_inr hc).elim

/-- Projection of an auxiliary source-to-sink path to its initial original-graph segment ending
at the first target. -/
structure TargetPathProjection {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink) where
  endpoint : {v : V // v ∈ T}
  walk : G.Walk u endpoint.1
  edge_subset : ∀ e ∈ walk.edges, Sym2.map targetAuxOriginal e ∈ p.edges

noncomputable def targetPathProjectionOfPath {T : Finset V} {k : ℕ} {u : V}
    (p : (targetAuxGraph G T k).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) : TargetPathProjection p := by
  let j := firstTargetIndex p hp
  let t : {v : V // v ∈ T} := Classical.choose (firstTargetIndex_spec p hp).2
  have ht : p.getVert j = targetAuxOriginal t.1 := by
    exact Classical.choose_spec (firstTargetIndex_spec p hp).2
  let q : (targetAuxGraph G T k).Walk (targetAuxOriginal u) (targetAuxOriginal t.1) :=
    (p.take j).copy rfl ht
  have hqOriginal : ∀ a ∈ q.support, a ∈ targetAuxOriginalSet T k := by
    intro a ha
    have ha' : a ∈ (p.take j).support := by simpa [q] using ha
    obtain ⟨v, hv⟩ := firstTargetPrefix_support_original p hp a ha'
    exact ⟨v, hv.symm⟩
  let qind := q.induce (targetAuxOriginalSet T k) hqOriginal
  let r₀ := qind.map (targetAuxOriginalSetHom T k)
  have hrstart : targetAuxOriginalGet
      (⟨targetAuxOriginal u, hqOriginal _ q.start_mem_support⟩ : targetAuxOriginalSet T k) = u := by
    apply Sum.inl.inj
    exact targetAuxOriginalGet_spec _
  have hrend : targetAuxOriginalGet
      (⟨targetAuxOriginal t.1, hqOriginal _ q.end_mem_support⟩ : targetAuxOriginalSet T k) =
      t.1 := by
    apply Sum.inl.inj
    exact targetAuxOriginalGet_spec _
  let r : G.Walk u t.1 := r₀.copy hrstart hrend
  refine ⟨t, r, ?_⟩
  intro e he
  have hind := congrArg SimpleGraph.Walk.edges (SimpleGraph.Walk.map_induce q hqOriginal)
  have hget : ∀ a : targetAuxOriginalSet T k,
      targetAuxOriginal (targetAuxOriginalGet a) = a.1 := targetAuxOriginalGet_spec
  have hedgeEq : r.edges.map (Sym2.map targetAuxOriginal) = q.edges := by
    calc
      r.edges.map (Sym2.map targetAuxOriginal) =
          (qind.map (targetAuxOriginalSetHom T k)).edges.map
            (Sym2.map targetAuxOriginal) := by simp [r, r₀]
      _ = qind.edges.map (Sym2.map fun a ↦
          targetAuxOriginal (targetAuxOriginalGet a)) := by
        simp [SimpleGraph.Walk.edges_map, List.map_map, Sym2.map_map,
          targetAuxOriginalSetHom, Function.comp_def]
      _ = qind.edges.map (Sym2.map fun a ↦ a.1) := by
        apply List.map_congr_left
        intro f _hf
        apply Sym2.map_congr
        intro a _ha
        exact hget a
      _ = q.edges := by
        rw [SimpleGraph.Walk.edges_map] at hind
        exact hind
  have heq : Sym2.map targetAuxOriginal e ∈ q.edges := by
    rw [← hedgeEq]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have heTake : Sym2.map targetAuxOriginal e ∈ (p.take j).edges := by
    simpa [q] using heq
  exact (SimpleGraph.Walk.isSubwalk_take p j).edges_subset heTake

/-- A walk from a fixed source to some member of a finite terminal set. -/
structure WalkToFinset (G : SimpleGraph V) (u : V) (T : Finset V) where
  endpoint : {v : V // v ∈ T}
  walk : G.Walk u endpoint.1

/-- **Arbitrary finite edge Menger theorem from one source to a finite target set.** -/
theorem isEdgeReachableToFinset_iff_exists_pairwise_edgeDisjoint_walks [Fintype V]
    {T : Finset V} {u : V} {k : ℕ} :
    IsEdgeReachableToFinset G k u T ↔
      ∃ P : Fin k → WalkToFinset G u T,
        Pairwise fun i j ↦ (P i).walk.edges.Disjoint (P j).walk.edges := by
  classical
  constructor
  · intro hreach
    have haux := targetAux_isEdgeReachable hreach
    obtain ⟨Q, hQpath, hQdisj⟩ :=
      (isEdgeReachable_iff_exists_pairwise_edgeDisjoint_paths).mp haux
    let project (i : Fin k) := targetPathProjectionOfPath (Q i) (hQpath i)
    let P : Fin k → WalkToFinset G u T := fun i ↦
      { endpoint := (project i).endpoint
        walk := (project i).walk }
    refine ⟨P, ?_⟩
    intro i j hij
    rw [List.disjoint_left]
    intro e hei hej
    exact List.disjoint_left.mp (hQdisj hij)
      ((project i).edge_subset e hei) ((project j).edge_subset e hej)
  · rintro ⟨P, hP⟩ s hs
    by_contra hno
    push Not at hno
    have hall : ∀ i : Fin k, ∃ e, e ∈ (P i).walk.edges ∧ e ∈ s := by
      intro i
      exact hno (P i).endpoint.1 (P i).endpoint.2 (P i).walk
    have hsFinite : s.Finite := Set.finite_of_encard_le_coe hs.le
    letI : Fintype s := hsFinite.fintype
    let chosen : Fin k → Sym2 V := fun i ↦ Classical.choose (hall i)
    have chosen_mem_walk (i : Fin k) : chosen i ∈ (P i).walk.edges :=
      (Classical.choose_spec (hall i)).1
    have chosen_mem_s (i : Fin k) : chosen i ∈ s :=
      (Classical.choose_spec (hall i)).2
    let f : Fin k → s := fun i ↦ ⟨chosen i, chosen_mem_s i⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hchosen : chosen i = chosen j := Subtype.ext_iff.mp hij
      have hjmem : chosen i ∈ (P j).walk.edges := by
        rw [hchosen]
        exact chosen_mem_walk j
      exact List.disjoint_left.mp (hP hne) (chosen_mem_walk i)
        hjmem
    have hk : k ≤ Fintype.card s := by
      simpa using Fintype.card_le_of_injective f hf
    have hk' : (k : ℕ∞) ≤ (Fintype.card s : ℕ∞) := ENat.coe_le_coe.mpr hk
    rw [Set.coe_fintypeCard] at hk'
    exact (not_le_of_gt hs) hk'

omit [DecidableEq V] in
def targetAuxOriginalEmbedding (T : Finset V) (k : ℕ) :
    V ↪ TargetAuxVertex T k where
  toFun := targetAuxOriginal
  inj' := targetAuxOriginal_injective

def targetAuxOriginalFinset (A B : Finset V) (k : ℕ) :
    Finset (TargetAuxVertex A k) :=
  B.map (targetAuxOriginalEmbedding A k)

omit [DecidableEq V] in
@[simp]
theorem targetAuxOriginal_mem_originalFinset {A B : Finset V} {k : ℕ} (b : V) :
    targetAuxOriginal (T := A) (k := k) b ∈ targetAuxOriginalFinset A B k ↔ b ∈ B := by
  simp [targetAuxOriginalFinset, targetAuxOriginalEmbedding]

/-- The two-edge private channel from the common sink back to an original terminal. -/
def walkFromTargetAuxSink {A : Finset V} {k : ℕ} (a : {v : V // v ∈ A})
    (i : Fin k) :
    (targetAuxGraph G A k).Walk targetAuxSink (targetAuxOriginal a.1) :=
  (SimpleGraph.Walk.nil.concat (targetAuxGraph_adj_sink a i).symm).concat
    (targetAuxGraph_adj_channel a i).symm

omit [DecidableEq V] in
theorem walkFromTargetAuxSink_edges {A : Finset V} {k : ℕ}
    (a : {v : V // v ∈ A}) (i : Fin k) :
    (walkFromTargetAuxSink (G := G) a i).edges =
      [s(targetAuxChannel a i, targetAuxSink),
        s(targetAuxOriginal a.1, targetAuxChannel a i)] := by
  unfold walkFromTargetAuxSink
  rw [SimpleGraph.Walk.edges_concat, SimpleGraph.Walk.edges_concat]
  simp [List.concat_eq_append]

/-- Cut-survival between two finite terminal sets. -/
def IsEdgeReachableBetweenFinsets (G : SimpleGraph V) (k : ℕ)
    (A B : Finset V) : Prop :=
  ∀ s : Set (Sym2 V), s.encard < (k : ℕ) →
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, ∀ e ∈ p.edges, e ∉ s

omit [DecidableEq V] in
theorem isEdgeReachableBetweenFinsets_zero (G : SimpleGraph V)
    (A B : Finset V) : IsEdgeReachableBetweenFinsets G 0 A B := by
  intro s hs
  simp at hs

omit [DecidableEq V] in
/-- Turning the left terminal set into a private-channel source fan reduces set-to-set
cut-survival to the one-source terminal theorem. -/
theorem targetAuxSink_isEdgeReachableToFinset {A B : Finset V} {k : ℕ}
    (hreach : IsEdgeReachableBetweenFinsets G k A B) :
    IsEdgeReachableToFinset (targetAuxGraph G A k) k targetAuxSink
      (targetAuxOriginalFinset A B k) := by
  classical
  intro s hs
  let f : Sym2 V → Sym2 (TargetAuxVertex A k) := Sym2.map targetAuxOriginal
  let originalDeleted : Set (Sym2 V) := f ⁻¹' s
  have hf : Function.Injective f := Sym2.map.injective targetAuxOriginal_injective
  have hdeletedCard : originalDeleted.encard ≤ s.encard := by
    calc
      originalDeleted.encard = (f '' originalDeleted).encard :=
        (hf.encard_image originalDeleted).symm
      _ ≤ s.encard := Set.encard_mono (Set.image_preimage_subset f s)
  have hdeletedLt : originalDeleted.encard < (k : ℕ) := hdeletedCard.trans_lt hs
  obtain ⟨a, ha, b, hb, p, hp⟩ := hreach originalDeleted hdeletedLt
  obtain ⟨i, hiEntry, hiExit⟩ :=
    exists_targetAux_channel_avoiding (⟨a, ha⟩ : {v : V // v ∈ A}) s hs
  let q : (targetAuxGraph G A k).Walk targetAuxSink (targetAuxOriginal b) :=
    (walkFromTargetAuxSink (G := G) (⟨a, ha⟩ : {v : V // v ∈ A}) i).append
      (p.map (targetAuxOriginalHom A k))
  refine ⟨targetAuxOriginal b, (targetAuxOriginal_mem_originalFinset b).2 hb, q, ?_⟩
  intro e he
  change e ∈ ((walkFromTargetAuxSink (G := G)
    (⟨a, ha⟩ : {v : V // v ∈ A}) i).append
      (p.map (targetAuxOriginalHom A k))).edges at he
  rw [SimpleGraph.Walk.edges_append, walkFromTargetAuxSink_edges] at he
  rcases List.mem_append.mp he with hchannel | horiginal
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hchannel
    rcases hchannel with hchannel | hchannel
    · simpa only [hchannel] using hiExit
    · simpa only [hchannel] using hiEntry
  · have hmapEdges : (p.map (targetAuxOriginalHom A k)).edges =
        p.edges.map (Sym2.map (targetAuxOriginalHom A k)) :=
      SimpleGraph.Walk.edges_map (targetAuxOriginalHom A k) p
    have horiginal' : e ∈ p.edges.map (Sym2.map (targetAuxOriginalHom A k)) :=
      (congrArg (fun l ↦ e ∈ l) hmapEdges).mp horiginal
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp horiginal'
    exact hp e₀ he₀

/-- A walk joining some member of `A` to some member of `B`. -/
structure WalkBetweenFinsets (G : SimpleGraph V) (A B : Finset V) where
  start : {v : V // v ∈ A}
  finish : {v : V // v ∈ B}
  walk : G.Walk start.1 finish.1

private noncomputable def projectSourceFanPath {A B : Finset V} {k : ℕ}
    (Q : WalkToFinset (targetAuxGraph G A k) targetAuxSink
      (targetAuxOriginalFinset A B k)) :
    WalkBetweenFinsets G A B := by
  let b : {v : V // v ∈ B} := by
    refine ⟨Classical.choose (Finset.mem_map.mp Q.endpoint.2), ?_⟩
    exact (Classical.choose_spec (Finset.mem_map.mp Q.endpoint.2)).1
  have hbEq : Q.endpoint.1 = targetAuxOriginal b.1 := by
    simpa [targetAuxOriginalEmbedding] using
      (Classical.choose_spec (Finset.mem_map.mp Q.endpoint.2)).2.symm
  let q : (targetAuxGraph G A k).Walk targetAuxSink (targetAuxOriginal b.1) :=
    Q.walk.copy rfl hbEq
  let qpath : (targetAuxGraph G A k).Walk targetAuxSink (targetAuxOriginal b.1) :=
    q.toPath
  let qrev : (targetAuxGraph G A k).Walk (targetAuxOriginal b.1) targetAuxSink :=
    qpath.reverse
  have hqrev : qrev.IsPath := by
    exact SimpleGraph.Walk.IsPath.reverse q.toPath.2
  let R := targetPathProjectionOfPath qrev hqrev
  exact
    { start := R.endpoint
      finish := b
      walk := R.walk.reverse }

private theorem projectSourceFanPath_edge_maps_into {A B : Finset V} {k : ℕ}
    (Q : WalkToFinset (targetAuxGraph G A k) targetAuxSink
      (targetAuxOriginalFinset A B k))
    (e : Sym2 V) (he : e ∈ (projectSourceFanPath Q).walk.edges) :
    Sym2.map (targetAuxOriginal (T := A) (k := k)) e ∈ Q.walk.edges := by
  classical
  unfold projectSourceFanPath at he
  dsimp only at he
  -- Expose the same chosen endpoint and copied path used by the projection.
  let b : {v : V // v ∈ B} := by
    refine ⟨Classical.choose (Finset.mem_map.mp Q.endpoint.2), ?_⟩
    exact (Classical.choose_spec (Finset.mem_map.mp Q.endpoint.2)).1
  have hbEq : Q.endpoint.1 = targetAuxOriginal b.1 := by
    simpa [targetAuxOriginalEmbedding] using
      (Classical.choose_spec (Finset.mem_map.mp Q.endpoint.2)).2.symm
  let q : (targetAuxGraph G A k).Walk targetAuxSink (targetAuxOriginal b.1) :=
    Q.walk.copy rfl hbEq
  let qpath : (targetAuxGraph G A k).Walk targetAuxSink (targetAuxOriginal b.1) :=
    q.toPath
  let qrev : (targetAuxGraph G A k).Walk (targetAuxOriginal b.1) targetAuxSink :=
    qpath.reverse
  have hqrev : qrev.IsPath := SimpleGraph.Walk.IsPath.reverse q.toPath.2
  let R := targetPathProjectionOfPath qrev hqrev
  change e ∈ R.walk.reverse.edges at he
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
  have hmap : Sym2.map targetAuxOriginal e ∈ qrev.edges := R.edge_subset e he
  change Sym2.map targetAuxOriginal e ∈ qpath.reverse.edges at hmap
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hmap
  change Sym2.map targetAuxOriginal e ∈
    (q.toPath : (targetAuxGraph G A k).Walk targetAuxSink (targetAuxOriginal b.1)).edges at hmap
  have hqmem : Sym2.map targetAuxOriginal e ∈ q.edges := q.edges_toPath_subset hmap
  simpa [q] using hqmem

/-- **Finite set-to-set edge Menger theorem.** Survival of an `A`-to-`B` connection after
deleting fewer than `k` edges is equivalent to `k` pairwise edge-disjoint `A`-to-`B` walks. -/
theorem isEdgeReachableBetweenFinsets_iff_exists_pairwise_edgeDisjoint_walks [Fintype V]
    {A B : Finset V} {k : ℕ} :
    IsEdgeReachableBetweenFinsets G k A B ↔
      ∃ P : Fin k → WalkBetweenFinsets G A B,
        Pairwise fun i j ↦ (P i).walk.edges.Disjoint (P j).walk.edges := by
  classical
  constructor
  · intro hreach
    have hfan := targetAuxSink_isEdgeReachableToFinset hreach
    obtain ⟨Q, hQdisj⟩ :=
      (isEdgeReachableToFinset_iff_exists_pairwise_edgeDisjoint_walks).mp hfan
    let P : Fin k → WalkBetweenFinsets G A B := fun i ↦ projectSourceFanPath (Q i)
    refine ⟨P, ?_⟩
    intro i j hij
    rw [List.disjoint_left]
    intro e hei hej
    exact List.disjoint_left.mp (hQdisj hij)
      (projectSourceFanPath_edge_maps_into (Q i) e hei)
      (projectSourceFanPath_edge_maps_into (Q j) e hej)
  · rintro ⟨P, hP⟩ s hs
    by_contra hno
    push Not at hno
    have hall : ∀ i : Fin k, ∃ e, e ∈ (P i).walk.edges ∧ e ∈ s := by
      intro i
      exact hno (P i).start.1 (P i).start.2 (P i).finish.1 (P i).finish.2
        (P i).walk
    have hsFinite : s.Finite := Set.finite_of_encard_le_coe hs.le
    letI : Fintype s := hsFinite.fintype
    let chosen : Fin k → Sym2 V := fun i ↦ Classical.choose (hall i)
    have chosen_mem_walk (i : Fin k) : chosen i ∈ (P i).walk.edges :=
      (Classical.choose_spec (hall i)).1
    have chosen_mem_s (i : Fin k) : chosen i ∈ s :=
      (Classical.choose_spec (hall i)).2
    let f : Fin k → s := fun i ↦ ⟨chosen i, chosen_mem_s i⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hchosen : chosen i = chosen j := Subtype.ext_iff.mp hij
      have hjmem : chosen i ∈ (P j).walk.edges := by
        rw [hchosen]
        exact chosen_mem_walk j
      exact List.disjoint_left.mp (hP hne) (chosen_mem_walk i) hjmem
    have hk : k ≤ Fintype.card s := by
      simpa using Fintype.card_le_of_injective f hf
    have hk' : (k : ℕ∞) ≤ (Fintype.card s : ℕ∞) := ENat.coe_le_coe.mpr hk
    rw [Set.coe_fintypeCard] at hk'
    exact (not_le_of_gt hs) hk'

end EdgeMenger

end Percolation
