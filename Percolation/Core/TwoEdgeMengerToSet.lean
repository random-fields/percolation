import Percolation.Core.TwoEdgeMenger

/-!
# A finite two-edge Menger theorem to a target set

The ordinary one-target reduction introduces a spurious bottleneck when two edge-disjoint
paths end at the same target.  This file supplies two private terminal channels per target and
uses the finite two-edge theorem to prove the target-set form needed by Grimmett Lemma 5.12.
-/

namespace Percolation

namespace TwoEdgeMenger

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- Original vertices, two terminal-channel vertices for each target, and the common sink. -/
abbrev TargetAuxVertex (T : Finset V) :=
  Sum V (Sum ({v : V // v ∈ T} × Bool) Unit)

def targetAuxOriginal {T : Finset V} (v : V) : TargetAuxVertex T := Sum.inl v

def targetAuxChannel {T : Finset V} (t : {v : V // v ∈ T}) (b : Bool) :
    TargetAuxVertex T := Sum.inr (Sum.inl (t, b))

def targetAuxSink {T : Finset V} : TargetAuxVertex T := Sum.inr (Sum.inr ())

def targetAuxRel (G : SimpleGraph V) (T : Finset V) :
    TargetAuxVertex T → TargetAuxVertex T → Prop
  | Sum.inl u, Sum.inl v => G.Adj u v
  | Sum.inl u, Sum.inr (Sum.inl c) => u = c.1.1
  | Sum.inr (Sum.inl _c), Sum.inr (Sum.inr _) => True
  | _, _ => False

def targetAuxGraph (G : SimpleGraph V) (T : Finset V) : SimpleGraph (TargetAuxVertex T) :=
  SimpleGraph.fromRel (targetAuxRel G T)

omit [DecidableEq V] in
theorem targetAuxGraph_adj_original {T : Finset V} {u v : V} (h : G.Adj u v) :
    (targetAuxGraph G T).Adj (targetAuxOriginal u) (targetAuxOriginal v) := by
  rw [targetAuxGraph, SimpleGraph.fromRel_adj]
  exact ⟨fun huv ↦ h.ne (Sum.inl.inj huv), Or.inl h⟩

omit [DecidableEq V] in
theorem targetAuxGraph_adj_channel {T : Finset V} (t : {v : V // v ∈ T}) (b : Bool) :
    (targetAuxGraph G T).Adj (targetAuxOriginal t.1) (targetAuxChannel t b) := by
  rw [targetAuxGraph, SimpleGraph.fromRel_adj]
  simp [targetAuxRel, targetAuxOriginal, targetAuxChannel]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_sink {T : Finset V} (t : {v : V // v ∈ T}) (b : Bool) :
    (targetAuxGraph G T).Adj (targetAuxChannel t b) targetAuxSink := by
  rw [targetAuxGraph, SimpleGraph.fromRel_adj]
  simp [targetAuxRel, targetAuxChannel, targetAuxSink]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_original_iff {T : Finset V} {u : V}
    {v : TargetAuxVertex T} :
    (targetAuxGraph G T).Adj (targetAuxOriginal u) v ↔
      (∃ w, v = targetAuxOriginal w ∧ G.Adj u w) ∨
      (∃ c : {v : V // v ∈ T} × Bool, v = targetAuxChannel c.1 c.2 ∧ u = c.1.1) := by
  cases v with
  | inl w =>
      rw [targetAuxGraph, SimpleGraph.fromRel_adj]
      simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, G.adj_comm]
      exact fun h ↦ h.ne
  | inr v =>
      cases v with
      | inl c =>
          rcases c with ⟨t, b⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel]
      | inr sinkUnit =>
          rcases sinkUnit with ⟨⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_sink_iff {T : Finset V} {v : TargetAuxVertex T} :
    (targetAuxGraph G T).Adj v targetAuxSink ↔
      ∃ c : {v : V // v ∈ T} × Bool, v = targetAuxChannel c.1 c.2 := by
  cases v with
  | inl u =>
      rw [targetAuxGraph, SimpleGraph.fromRel_adj]
      simp [targetAuxRel, targetAuxChannel, targetAuxSink]
  | inr v =>
      cases v with
      | inl c =>
          rcases c with ⟨t, b⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxChannel, targetAuxSink]
      | inr sinkUnit =>
          rcases sinkUnit with ⟨⟩
          simp [targetAuxSink, targetAuxChannel]

omit [DecidableEq V] in
theorem targetAuxGraph_adj_channel_iff {T : Finset V}
    {c : {v : V // v ∈ T} × Bool} {v : TargetAuxVertex T} :
    (targetAuxGraph G T).Adj v (targetAuxChannel c.1 c.2) ↔
      v = targetAuxOriginal c.1.1 ∨ v = targetAuxSink := by
  cases v with
  | inl u =>
      rw [targetAuxGraph, SimpleGraph.fromRel_adj]
      simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, targetAuxSink]
  | inr v =>
      cases v with
      | inl c' =>
          rcases c with ⟨t, b⟩
          rcases c' with ⟨t', b'⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, targetAuxSink]
      | inr sinkUnit =>
          rcases sinkUnit with ⟨⟩
          rw [targetAuxGraph, SimpleGraph.fromRel_adj]
          simp [targetAuxRel, targetAuxOriginal, targetAuxChannel, targetAuxSink]

def targetAuxOriginalHom (T : Finset V) : G →g targetAuxGraph G T where
  toFun := targetAuxOriginal
  map_rel' := targetAuxGraph_adj_original

def walkToTargetAux {T : Finset V} {u t : V} (p : G.Walk u t)
    (ht : t ∈ T) (b : Bool) :
    (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink :=
  ((p.map (targetAuxOriginalHom T)).concat
    (targetAuxGraph_adj_channel ⟨t, ht⟩ b)).concat
      (targetAuxGraph_adj_sink ⟨t, ht⟩ b)

omit [DecidableEq V] in
theorem walkToTargetAux_edges {T : Finset V} {u t : V} (p : G.Walk u t)
    (ht : t ∈ T) (b : Bool) :
    (walkToTargetAux p ht b).edges =
      p.edges.map (Sym2.map targetAuxOriginal) ++
        [s(targetAuxOriginal t, targetAuxChannel ⟨t, ht⟩ b),
          s(targetAuxChannel ⟨t, ht⟩ b, targetAuxSink)] := by
  unfold walkToTargetAux
  change ((((p.map (targetAuxOriginalHom T)).concat
    (targetAuxGraph_adj_channel ⟨t, ht⟩ b)).concat
      (targetAuxGraph_adj_sink ⟨t, ht⟩ b)).edges) = _
  rw [SimpleGraph.Walk.edges_concat, SimpleGraph.Walk.edges_concat,
    SimpleGraph.Walk.edges_map]
  simp [List.concat_eq_append, targetAuxOriginalHom]

omit [DecidableEq V] in
theorem targetAuxChannel_not_mem_map_original {T : Finset V}
    (t : {v : V // v ∈ T}) (b : Bool) (e : Sym2 V) :
    targetAuxChannel t b ∉ Sym2.map targetAuxOriginal e := by
  intro h
  rw [Sym2.mem_map] at h
  obtain ⟨v, _hv, hv⟩ := h
  exact Sum.inl_ne_inr hv

omit [DecidableEq V] in
theorem targetAuxSink_not_mem_map_original {T : Finset V} (e : Sym2 V) :
    (targetAuxSink : TargetAuxVertex T) ∉ Sym2.map targetAuxOriginal e := by
  intro h
  rw [Sym2.mem_map] at h
  obtain ⟨v, _hv, hv⟩ := h
  exact Sum.inl_ne_inr hv

omit [DecidableEq V] in
theorem targetAux_channelEdge_ne_map_original {T : Finset V}
    (t : {v : V // v ∈ T}) (b : Bool) (e : Sym2 V) :
    s(targetAuxOriginal t.1, targetAuxChannel t b) ≠ Sym2.map targetAuxOriginal e := by
  intro h
  apply targetAuxChannel_not_mem_map_original t b e
  rw [← h]
  simp

omit [DecidableEq V] in
theorem targetAux_sinkEdge_ne_map_original {T : Finset V}
    (t : {v : V // v ∈ T}) (b : Bool) (e : Sym2 V) :
    s(targetAuxChannel t b, targetAuxSink) ≠ Sym2.map targetAuxOriginal e := by
  intro h
  apply targetAuxSink_not_mem_map_original e
  rw [← h]
  simp

omit [DecidableEq V] in
theorem toTargetAux_channels_edgeDisjoint {T : Finset V} {u t : V}
    (p : G.Walk u t) (ht : t ∈ T) :
    let p₀ := walkToTargetAux p ht false
    let p₁ := walkToTargetAux p ht true
    ∀ e, e ∈ p₀.edges → e ∈ p₁.edges →
      ∃ f ∈ p.edges, e = Sym2.map targetAuxOriginal f := by
  intro p₀ p₁ e he₀ he₁
  dsimp only [p₀, p₁] at he₀ he₁
  rw [walkToTargetAux_edges p ht false] at he₀
  rw [walkToTargetAux_edges p ht true] at he₁
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he₀ he₁
  rcases he₀ with he₀ | he₀ | he₀ <;> rcases he₁ with he₁ | he₁ | he₁
  · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he₀
    exact ⟨f, hf, hfe.symm⟩
  · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he₀
    exact (targetAux_channelEdge_ne_map_original ⟨t, ht⟩ true f
      (he₁.symm.trans hfe.symm)).elim
  · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he₀
    exact (targetAux_sinkEdge_ne_map_original ⟨t, ht⟩ true f
      (he₁.symm.trans hfe.symm)).elim
  · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he₁
    exact (targetAux_channelEdge_ne_map_original ⟨t, ht⟩ false f
      (he₀.symm.trans hfe.symm)).elim
  · exfalso
    subst e
    simp [targetAuxOriginal, targetAuxChannel] at he₁
  · exfalso
    subst e
    simp [targetAuxOriginal, targetAuxChannel, targetAuxSink] at he₁
  · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he₁
    exact (targetAux_sinkEdge_ne_map_original ⟨t, ht⟩ false f
      (he₀.symm.trans hfe.symm)).elim
  · exfalso
    subst e
    simp [targetAuxOriginal, targetAuxChannel, targetAuxSink] at he₁
  · exfalso
    subst e
    simp [targetAuxChannel, targetAuxSink] at he₁

omit [DecidableEq V] in
theorem map_original_not_mem_walkToTargetAux {T : Finset V} {u t : V}
    (p : G.Walk u t) (ht : t ∈ T) (b : Bool) {e : Sym2 V} (he : e ∉ p.edges) :
    Sym2.map targetAuxOriginal e ∉ (walkToTargetAux p ht b).edges := by
  rw [walkToTargetAux_edges p ht b]
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  rintro (⟨f, hf, hfe⟩ | h | h)
  · exact he ((Sym2.map.injective Sum.inl_injective) hfe ▸ hf)
  · exact targetAux_channelEdge_ne_map_original ⟨t, ht⟩ b e h.symm
  · exact targetAux_sinkEdge_ne_map_original ⟨t, ht⟩ b e h.symm

/-- Two-edge reachability from a vertex to a finite target set, encoded in the doubled-terminal
auxiliary graph. -/
theorem targetAux_isEdgeReachable_two [Fintype V] {T : Finset V} {u t₀ : V}
    (ht₀ : t₀ ∈ T) (p₀ : G.Walk u t₀)
    (havoid : ∀ e : Sym2 V, ∃ t ∈ T, ∃ p : G.Walk u t, e ∉ p.edges) :
    (targetAuxGraph G T).IsEdgeReachable 2 (targetAuxOriginal u) targetAuxSink := by
  classical
  let q₀ := walkToTargetAux p₀ ht₀ false
  let q₁ := walkToTargetAux p₀ ht₀ true
  apply isEdgeReachable_two_of_walks_and_overlap_avoidance q₀ q₁
  intro e he₀ he₁
  obtain ⟨f, hf, hef⟩ := toTargetAux_channels_edgeDisjoint p₀ ht₀ e he₀ he₁
  obtain ⟨t, ht, p, hfp⟩ := havoid f
  refine ⟨walkToTargetAux p ht false, ?_⟩
  rw [hef]
  exact map_original_not_mem_walkToTargetAux p ht false hfp

omit [DecidableEq V] in
theorem exists_target_original_mem_support {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink)
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
  let p₁ : (targetAuxGraph G T).Walk (targetAuxOriginal u) (targetAuxChannel c.1 c.2) :=
    p.dropLast.copy rfl hc
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
theorem firstTarget_exists {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) :
    ∃ k : ℕ, k ≤ p.length ∧
      ∃ t : {v : V // v ∈ T}, p.getVert k = targetAuxOriginal t.1 := by
  obtain ⟨t, ht, hmem⟩ := exists_target_original_mem_support p hp
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨k, hkt, hk⟩ := hmem
  exact ⟨k, hk, ⟨t, ht⟩, hkt⟩

noncomputable def firstTargetIndex {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) : ℕ := Nat.find (firstTarget_exists p hp)

theorem firstTargetIndex_spec {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) :
    firstTargetIndex p hp ≤ p.length ∧
      ∃ t : {v : V // v ∈ T},
        p.getVert (firstTargetIndex p hp) = targetAuxOriginal t.1 :=
  Nat.find_spec (firstTarget_exists p hp)

theorem getVert_eq_original_of_le_firstTargetIndex {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink)
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

theorem firstTargetPrefix_support_original {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink)
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

def targetAuxOriginalSet (T : Finset V) : Set (TargetAuxVertex T) :=
  Set.range targetAuxOriginal

noncomputable def targetAuxOriginalGet {T : Finset V}
    (a : targetAuxOriginalSet T) : V := Classical.choose a.2

omit [DecidableEq V] in
theorem targetAuxOriginalGet_spec {T : Finset V} (a : targetAuxOriginalSet T) :
    targetAuxOriginal (targetAuxOriginalGet a) = a.1 :=
  Classical.choose_spec a.2

omit [DecidableEq V] in
@[simp]
theorem targetAuxOriginalGet_mk {T : Finset V} (v : V) :
    targetAuxOriginalGet
      (⟨targetAuxOriginal v, ⟨v, rfl⟩⟩ : targetAuxOriginalSet T) = v := by
  apply Sum.inl.inj
  exact targetAuxOriginalGet_spec _

noncomputable def targetAuxOriginalSetHom (T : Finset V) :
    (targetAuxGraph G T).induce (targetAuxOriginalSet T) →g G where
  toFun := targetAuxOriginalGet
  map_rel' := by
    intro a b hab
    have hab' : (targetAuxGraph G T).Adj a.1 b.1 := SimpleGraph.induce_adj.mp hab
    rw [← targetAuxOriginalGet_spec a, ← targetAuxOriginalGet_spec b] at hab'
    rcases targetAuxGraph_adj_original_iff.mp hab' with h | h
    · obtain ⟨w, hw, hadj⟩ := h
      have hw' : w = targetAuxOriginalGet b := Sum.inl.inj hw.symm
      simpa [hw'] using hadj
    · obtain ⟨c, hc, _⟩ := h
      exact (Sum.inl_ne_inr hc).elim

structure TargetPathProjection {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink) where
  endpoint : {v : V // v ∈ T}
  walk : G.Walk u endpoint.1
  edge_subset : ∀ e ∈ walk.edges, Sym2.map targetAuxOriginal e ∈ p.edges

noncomputable def targetPathProjectionOfPath {T : Finset V} {u : V}
    (p : (targetAuxGraph G T).Walk (targetAuxOriginal u) targetAuxSink)
    (hp : p.IsPath) : TargetPathProjection p := by
  let k := firstTargetIndex p hp
  let t : {v : V // v ∈ T} := Classical.choose (firstTargetIndex_spec p hp).2
  have ht : p.getVert k = targetAuxOriginal t.1 := by
    exact Classical.choose_spec (firstTargetIndex_spec p hp).2
  let q : (targetAuxGraph G T).Walk (targetAuxOriginal u) (targetAuxOriginal t.1) :=
    (p.take k).copy rfl ht
  have hqOriginal : ∀ a ∈ q.support, a ∈ targetAuxOriginalSet T := by
    intro a ha
    have ha' : a ∈ (p.take k).support := by simpa [q] using ha
    obtain ⟨v, hv⟩ := firstTargetPrefix_support_original p hp a ha'
    exact ⟨v, hv.symm⟩
  let qind := q.induce (targetAuxOriginalSet T) hqOriginal
  let r₀ := qind.map (targetAuxOriginalSetHom T)
  have hrstart : targetAuxOriginalGet
      (⟨targetAuxOriginal u, hqOriginal _ q.start_mem_support⟩ : targetAuxOriginalSet T) = u := by
    apply Sum.inl.inj
    exact targetAuxOriginalGet_spec _
  have hrend : targetAuxOriginalGet
      (⟨targetAuxOriginal t.1, hqOriginal _ q.end_mem_support⟩ : targetAuxOriginalSet T) = t.1 := by
    apply Sum.inl.inj
    exact targetAuxOriginalGet_spec _
  let r : G.Walk u t.1 := r₀.copy hrstart hrend
  refine ⟨t, r, ?_⟩
  intro e he
  have hind := congrArg SimpleGraph.Walk.edges (SimpleGraph.Walk.map_induce q hqOriginal)
  have hget : ∀ a : targetAuxOriginalSet T,
      targetAuxOriginal (targetAuxOriginalGet a) = a.1 := targetAuxOriginalGet_spec
  have hedgeEq : r.edges.map (Sym2.map targetAuxOriginal) = q.edges := by
    calc
      r.edges.map (Sym2.map targetAuxOriginal) =
          (qind.map (targetAuxOriginalSetHom T)).edges.map
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
  have heTake : Sym2.map targetAuxOriginal e ∈ (p.take k).edges := by
    simpa [q] using heq
  exact (SimpleGraph.Walk.isSubwalk_take p k).edges_subset heTake

/-- **Finite two-edge Menger theorem to a target set.** If deletion of every edge leaves a
walk from `u` to some vertex of `T`, then two edge-disjoint walks from `u` to (not necessarily
distinct) vertices of `T` exist. -/
theorem exists_two_edgeDisjoint_walks_to_finset [Fintype V]
    {T : Finset V} {u t₀ : V} (ht₀ : t₀ ∈ T) (p₀ : G.Walk u t₀)
    (havoid : ∀ e : Sym2 V, ∃ t ∈ T, ∃ p : G.Walk u t, e ∉ p.edges) :
    ∃ t₁ : {v : V // v ∈ T}, ∃ t₂ : {v : V // v ∈ T},
      ∃ p : G.Walk u t₁.1, ∃ q : G.Walk u t₂.1, p.edges.Disjoint q.edges := by
  classical
  have hreach := targetAux_isEdgeReachable_two ht₀ p₀ havoid
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    exists_two_edgeDisjoint_paths_of_isEdgeReachable_two hreach
  let P := targetPathProjectionOfPath p hp
  let Q := targetPathProjectionOfPath q hq
  refine ⟨P.endpoint, Q.endpoint, P.walk, Q.walk, List.disjoint_left.mpr ?_⟩
  intro e heP heQ
  exact List.disjoint_left.mp hpq (P.edge_subset e heP) (Q.edge_subset e heQ)

end TwoEdgeMenger

end Percolation
