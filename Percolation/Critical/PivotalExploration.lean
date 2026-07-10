import Percolation.Critical.PivotalSausage

/-!
# Finite exploration at a pivotal edge

This file develops the deleted-cluster geometry used in Grimmett's conditioning
argument for Lemma 5.12.  The key invariant is the finite set reachable from the
origin after the marked pivotal edge is deleted.
-/

namespace Percolation

open scoped BigOperators

/-- Ball vertices reachable from `x` inside the radius support after deleting
the edge `e`.  This is Grimmett's finite `D_e`. -/
noncomputable def radiusDeletedReachableVertices
    (d : ℕ) (x : Cubic d) (n : ℕ) (e : CubicEdge d)
    (omega : EdgeConfiguration d) : Finset (Cubic d) := by
  classical
  exact (cubicMetricBall d x n).filter fun y ↦
    omega \ {e} ∈ connectionEventIn d
      ((cubicMetricBallEdges d x n).erase e) x y

@[simp]
theorem mem_radiusDeletedReachableVertices_iff
    {d n : ℕ} {x y : Cubic d} {e : CubicEdge d}
    {omega : EdgeConfiguration d} :
    y ∈ radiusDeletedReachableVertices d x n e omega ↔
      y ∈ cubicMetricBall d x n ∧
      omega \ {e} ∈ connectionEventIn d
        ((cubicMetricBallEdges d x n).erase e) x y := by
  classical
  simp [radiusDeletedReachableVertices]

private theorem edge_getElem_eq_dart_edge {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) {i : ℕ} (hi : i < w.darts.length) :
    w.edges[i]'(by simpa using hi) = w.darts[i].edge := by
  have hiE : i < w.edges.length := by simpa using hi
  induction w generalizing i with
  | nil => simp at hi
  | cons h p ih =>
      cases i with
      | zero => simp [SimpleGraph.Walk.edges]
      | succ i =>
          simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.darts_cons,
            List.getElem_cons_succ]
          apply ih
          simpa using hiE

private theorem dart_edge_mem_edges_drop {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) {i : ℕ} (hi : i < w.darts.length) :
    w.darts[i].edge ∈ w.edges.drop i := by
  have hiE : i < w.edges.length := by simpa using hi
  rw [← edge_getElem_eq_dart_edge w hi]
  have hzero : 0 < (w.edges.drop i).length := by simp only [List.length_drop]; omega
  have hmem : (w.edges.drop i)[0] ∈ w.edges.drop i := List.getElem_mem hzero
  simpa [hiE] using hmem

private theorem dart_edge_not_mem_edges_take {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hw : w.IsTrail)
    {i : ℕ} (hi : i < w.darts.length) :
    w.darts[i].edge ∉ w.edges.take i := by
  intro htake
  exact (List.disjoint_take_drop hw.edges_nodup (le_refl i)) htake
    (dart_edge_mem_edges_drop w hi)

private theorem dart_edge_not_mem_edges_drop_succ {d : ℕ} {u v : Cubic d}
    (w : (cubicGraph d).Walk u v) (hw : w.IsTrail)
    {i : ℕ} (hi : i < w.darts.length) :
    w.darts[i].edge ∉ w.edges.drop (i + 1) := by
  intro hdrop
  have hiE : i < w.edges.length := by simpa using hi
  have htake : w.darts[i].edge ∈ w.edges.take (i + 1) := by
    rw [← edge_getElem_eq_dart_edge w hi]
    have hiTake : i < (w.edges.take (i + 1)).length := by
      simp only [List.length_take]; omega
    have hmem : (w.edges.take (i + 1))[i] ∈ w.edges.take (i + 1) :=
      List.getElem_mem hiTake
    simpa [hiE] using hmem
  exact (List.disjoint_take_drop hw.edges_nodup (le_refl (i + 1))) htake hdrop

private theorem walkIsOpen_diff_singleton_take_before_dart
    {d : ℕ} {u v : Cubic d} {omega : EdgeConfiguration d}
    (w : (cubicGraph d).Walk u v) (hpath : w.IsPath)
    (hopen : walkIsOpen omega w) {i : ℕ} (hi : i < w.darts.length) :
    walkIsOpen (omega \ {cubicEdgeOfDart w.darts[i]}) (w.take i) := by
  intro f hf
  have hfW : f ∈ w.edges := by
    rw [SimpleGraph.Walk.edges_take] at hf
    exact List.mem_of_mem_take hf
  refine ⟨hopen f hfW, ?_⟩
  intro hfe
  have hval : f = w.darts[i].edge := by
    simpa [cubicEdgeOfDart] using congrArg Subtype.val hfe
  exact dart_edge_not_mem_edges_take w hpath.isTrail hi (hval ▸ by
    simpa [SimpleGraph.Walk.edges_take] using hf)

private theorem walkIsOpen_diff_singleton_drop_after_dart
    {d : ℕ} {u v : Cubic d} {omega : EdgeConfiguration d}
    (w : (cubicGraph d).Walk u v) (hpath : w.IsPath)
    (hopen : walkIsOpen omega w) {i : ℕ} (hi : i < w.darts.length) :
    walkIsOpen (omega \ {cubicEdgeOfDart w.darts[i]}) (w.drop (i + 1)) := by
  intro f hf
  have hfW : f ∈ w.edges := by
    rw [SimpleGraph.Walk.edges_drop] at hf
    exact List.mem_of_mem_drop hf
  refine ⟨hopen f hfW, ?_⟩
  intro hfe
  have hval : f = w.darts[i].edge := by
    simpa [cubicEdgeOfDart] using congrArg Subtype.val hfe
  exact dart_edge_not_mem_edges_drop_succ w hpath.isTrail hi (hval ▸ by
    simpa [SimpleGraph.Walk.edges_drop] using hf)

/-- The tail of the canonical witness after a selected dart begins at that
dart's second endpoint. -/
private noncomputable def canonicalTailAfterDart
    {d n : ℕ} {x : Cubic d} {omega : EdgeConfiguration d}
    (homega : omega ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart}
    (ha : a ∈ (canonicalRadiusWitness homega).walk.darts) :
    (cubicGraph d).Walk a.snd (canonicalRadiusWitness homega).endpoint := by
  let W := canonicalRadiusWitness homega
  let i := (W.walk.darts).idxOf a
  have hi : i < W.walk.darts.length := List.idxOf_lt_length_iff.2 ha
  exact (W.walk.drop (i + 1)).copy (by
    have hget := W.walk.darts_getElem_eq_getVert i hi
    rw [List.getElem_idxOf hi] at hget
    exact congrArg (fun q ↦ q.toProd.2) hget |>.symm) rfl

/-- The oriented first endpoint of a pivotal dart lies in its deleted reachable
set. -/
theorem pivotalDart_fst_mem_radiusDeletedReachableVertices
    {d n : ℕ} {x : Cubic d} {omega : EdgeConfiguration d}
    (homega : omega ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts homega) :
    a.toProd.1 ∈ radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) omega := by
  classical
  let W := canonicalRadiusWitness homega
  have haW := (mem_radiusPivotalDarts_iff homega a).mp ha |>.1
  let i := W.walk.darts.idxOf a
  have hi : i < W.walk.darts.length := List.idxOf_lt_length_iff.2 haW
  have hget : W.walk.darts[i] = a := List.getElem_idxOf hi
  have hfst : W.walk.getVert i = a.toProd.1 := by
    have hdart := W.walk.darts_getElem_eq_getVert i hi
    rw [hget] at hdart
    exact congrArg (fun q ↦ q.toProd.1) hdart |>.symm
  have hball : a.toProd.1 ∈ cubicMetricBall d x n := by
    apply walk_support_subset_cubicMetricBall_of_edges (by simp) W.walk W.edge_subset
    rw [← hfst]
    exact W.walk.getVert_mem_support i
  rw [mem_radiusDeletedReachableVertices_iff]
  refine ⟨hball, ?_⟩
  let q := (W.walk.take i).copy rfl hfst
  refine ⟨q, ?_, ?_⟩
  · have hopen := walkIsOpen_diff_singleton_take_before_dart
      W.walk W.isPath W.isOpen hi
    simpa [q, hget] using (walkIsOpen_copy (W.walk.take i) rfl hfst).2 hopen
  · intro e he
    apply Finset.mem_erase.mpr
    constructor
    · intro heeq
      have heval := congrArg Subtype.val heeq
      have heTake : (e : Sym2 (Cubic d)) ∈ W.walk.edges.take i := by
        have he' := (mem_walkEdgeFinset_iff q e).mp he
        have he'' : (e : Sym2 (Cubic d)) ∈ (W.walk.take i).edges := by
          simpa [q] using he'
        rwa [SimpleGraph.Walk.edges_take] at he''
      have hval : (e : Sym2 (Cubic d)) = a.edge := by simpa [cubicEdgeOfDart] using heval
      have htake : a.edge ∈ W.walk.edges.take i := hval ▸ heTake
      exact dart_edge_not_mem_edges_take W.walk W.isPath.isTrail hi (by simpa [hget] using htake)
    · apply W.edge_subset
      rw [mem_walkEdgeFinset_iff]
      have heq : (e : Sym2 (Cubic d)) ∈ W.walk.edges.take i := by
        have he' := (mem_walkEdgeFinset_iff q e).mp he
        have he'' : (e : Sym2 (Cubic d)) ∈ (W.walk.take i).edges := by
          simpa [q] using he'
        rwa [SimpleGraph.Walk.edges_take] at he''
      exact List.mem_of_mem_take heq

/-- The oriented second endpoint of a pivotal dart is not reachable from the
origin after that edge is deleted.  Thus the canonical orientation agrees with
the two sides of the pivotal cut. -/
theorem pivotalDart_snd_not_mem_radiusDeletedReachableVertices
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    a.toProd.2 ∉ radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω := by
  classical
  let W := canonicalRadiusWitness hω
  have haData := (mem_radiusPivotalDarts_iff hω a).mp ha
  have haW : a ∈ W.walk.darts := haData.1
  have haPiv : IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart a) ω :=
    haData.2
  let i := W.walk.darts.idxOf a
  have hi : i < W.walk.darts.length := List.idxOf_lt_length_iff.2 haW
  have hget : W.walk.darts[i] = a := List.getElem_idxOf hi
  have hsnd : W.walk.getVert (i + 1) = a.toProd.2 := by
    have hdart := W.walk.darts_getElem_eq_getVert i hi
    rw [hget] at hdart
    exact congrArg (fun q ↦ q.toProd.2) hdart |>.symm
  intro hreach
  have hreach' := (mem_radiusDeletedReachableVertices_iff.mp hreach).2
  rcases hreach' with ⟨q, hqopen, hqsub⟩
  let t : (cubicGraph d).Walk a.toProd.2 W.endpoint :=
    (W.walk.drop (i + 1)).copy hsnd rfl
  have htopen : walkIsOpen (ω \ {cubicEdgeOfDart a}) t := by
    have h := walkIsOpen_diff_singleton_drop_after_dart W.walk W.isPath W.isOpen hi
    rw [hget] at h
    exact (walkIsOpen_copy (W.walk.drop (i + 1)) hsnd rfl).mpr h
  have happopen : walkIsOpen (ω \ {cubicEdgeOfDart a}) (q.append t) :=
    walkIsOpen_append hqopen htopen
  have happsub : walkEdgeFinset (q.append t) ⊆
      (cubicMetricBallEdges d x n).erase (cubicEdgeOfDart a) := by
    intro e he
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
      List.mem_append] at he
    rcases he with heq | het
    · exact hqsub ((mem_walkEdgeFinset_iff q e).mpr heq)
    · apply Finset.mem_erase.mpr
      constructor
      · intro hea
        have heval : (e : Sym2 (Cubic d)) = a.edge := by
          simpa [cubicEdgeOfDart] using congrArg Subtype.val hea
        have het' : a.edge ∈ W.walk.edges.drop (i + 1) := by
          have : (e : Sym2 (Cubic d)) ∈ (W.walk.drop (i + 1)).edges := by
            simpa [t] using het
          rw [SimpleGraph.Walk.edges_drop] at this
          exact heval ▸ this
        exact dart_edge_not_mem_edges_drop_succ W.walk W.isPath.isTrail hi
          (by simpa [hget] using het')
      · apply W.edge_subset
        rw [mem_walkEdgeFinset_iff]
        have : (e : Sym2 (Cubic d)) ∈ (W.walk.drop (i + 1)).edges := by
          simpa [t] using het
        rw [SimpleGraph.Walk.edges_drop] at this
        exact List.mem_of_mem_drop this
  have hclosed : ω \ {cubicEdgeOfDart a} ∈ radiusConnectionEvent d x n :=
    ⟨W.endpoint, W.sphere_mem, q.append t, happopen,
      happsub.trans (Finset.erase_subset _ _)⟩
  exact ((isIncreasingEvent_radiusConnectionEvent d x n).isPivotal_iff
    (cubicEdgeOfDart a) ω).mp haPiv |>.2 hclosed

@[simp]
theorem center_mem_radiusDeletedReachableVertices
    (d n : ℕ) (x : Cubic d) (e : CubicEdge d) (ω : EdgeConfiguration d) :
    x ∈ radiusDeletedReachableVertices d x n e ω := by
  classical
  rw [mem_radiusDeletedReachableVertices_iff]
  refine ⟨by simp, SimpleGraph.Walk.nil, ?_, ?_⟩
  · simp [walkIsOpen]
  · simp [walkEdgeFinset, walkEdgeList]

/-- A pivotal deleted cluster cannot reach the target sphere. -/
theorem radiusDeletedReachableVertices_disjoint_sphere_of_pivotal
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {e : CubicEdge d}
    (he : IsPivotal (radiusConnectionEvent d x n) e ω) :
    Disjoint (radiusDeletedReachableVertices d x n e ω)
      (cubicMetricSphere d x n) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyD hyS
  have hconn := (mem_radiusDeletedReachableVertices_iff.mp hyD).2
  rcases hconn with ⟨q, hqopen, hqsub⟩
  have hclosed : ω \ {e} ∈ radiusConnectionEvent d x n :=
    ⟨y, hyS, q, hqopen, hqsub.trans (Finset.erase_subset _ _)⟩
  exact ((isIncreasingEvent_radiusConnectionEvent d x n).isPivotal_iff e ω).mp he |>.2
    hclosed

/-- Whether an unoriented edge has one endpoint in `D` and one endpoint outside
`D`. -/
def cubicEdgeCrossesFinset {d : ℕ} (D : Finset (Cubic d))
    (e : CubicEdge d) : Prop :=
  Sym2.lift ⟨fun u v ↦ (u ∈ D ∧ v ∉ D) ∨ (v ∈ D ∧ u ∉ D), by
    intro u v
    aesop⟩ e.1

noncomputable instance {d : ℕ} (D : Finset (Cubic d)) (e : CubicEdge d) :
    Decidable (cubicEdgeCrossesFinset D e) := by
  exact Classical.propDecidable _

@[simp]
theorem cubicEdgeCrossesFinset_mk {d : ℕ} (D : Finset (Cubic d))
    {u v : Cubic d} (huv : (cubicGraph d).Adj u v) :
    cubicEdgeCrossesFinset D ⟨s(u, v), by
      rw [SimpleGraph.mem_edgeSet]
      exact huv⟩ ↔
      (u ∈ D ∧ v ∉ D) ∨ (v ∈ D ∧ u ∉ D) := by
  simp [cubicEdgeCrossesFinset, Sym2.lift_mk]

/-- Boundary edges of the deleted reachable set, restricted to the finite
radius support. -/
noncomputable def radiusDeletedBoundaryEdges
    (d : ℕ) (x : Cubic d) (n : ℕ) (e : CubicEdge d)
    (ω : EdgeConfiguration d) : Finset (CubicEdge d) := by
  classical
  exact (cubicMetricBallEdges d x n).filter fun f ↦
    cubicEdgeCrossesFinset (radiusDeletedReachableVertices d x n e ω) f

@[simp]
theorem mem_radiusDeletedBoundaryEdges_iff
    {d n : ℕ} {x : Cubic d} {e f : CubicEdge d}
    {ω : EdgeConfiguration d} :
    f ∈ radiusDeletedBoundaryEdges d x n e ω ↔
      f ∈ cubicMetricBallEdges d x n ∧
      cubicEdgeCrossesFinset (radiusDeletedReachableVertices d x n e ω) f := by
  classical
  simp [radiusDeletedBoundaryEdges]

/-- Apart from the deleted pivotal edge itself, every edge leaving its
reachable set is closed.  This is condition (a)--(c) in Grimmett's event
`B_e`, expressed without an informal conditional graph. -/
theorem mem_radiusDeletedBoundaryEdges_of_open_imp_eq
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {e f : CubicEdge d}
    (hfB : f ∈ radiusDeletedBoundaryEdges d x n e ω)
    (hfω : f ∈ ω) : f = e := by
  classical
  by_contra hfe
  rcases f with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v =>
      have huv : (cubicGraph d).Adj u v := by
        rw [← SimpleGraph.mem_edgeSet]
        exact hz
      have hcross := (mem_radiusDeletedBoundaryEdges_iff.mp hfB).2
      rw [cubicEdgeCrossesFinset_mk _ huv] at hcross
      rcases hcross with ⟨huD, hvD⟩ | ⟨hvD, huD⟩
      · have huConn := (mem_radiusDeletedReachableVertices_iff.mp huD).2
        rcases huConn with ⟨q, hqopen, hqsub⟩
        let step : (cubicGraph d).Walk u v := SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
        have hfdel : (⟨s(u, v), hz⟩ : CubicEdge d) ∈ ω \ {e} := by
          exact ⟨hfω, by simpa using hfe⟩
        have hstepopen : walkIsOpen (ω \ {e}) step := by
          intro g hg
          simp only [step, SimpleGraph.Walk.edges_cons,
            SimpleGraph.Walk.edges_nil, List.mem_singleton] at hg
          subst g
          simpa [edgeOpen] using hfdel
        have happopen := walkIsOpen_append hqopen hstepopen
        have happsub : walkEdgeFinset (q.append step) ⊆
            (cubicMetricBallEdges d x n).erase e := by
          intro g hg
          rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
            List.mem_append] at hg
          rcases hg with hg | hg
          · exact hqsub ((mem_walkEdgeFinset_iff q g).mpr hg)
          · have hgf : g = ⟨s(u, v), hz⟩ := by
              apply Subtype.ext
              simpa [step] using hg
            subst g
            apply Finset.mem_erase.mpr
            exact ⟨hfe, (mem_radiusDeletedBoundaryEdges_iff.mp hfB).1⟩
        apply hvD
        rw [mem_radiusDeletedReachableVertices_iff]
        refine ⟨endpoint_mem_cubicMetricBall_of_edge_mem
          (mem_radiusDeletedBoundaryEdges_iff.mp hfB).1 (by simp), ?_⟩
        exact ⟨q.append step, happopen, happsub⟩
      · have hvConn := (mem_radiusDeletedReachableVertices_iff.mp hvD).2
        rcases hvConn with ⟨q, hqopen, hqsub⟩
        let step : (cubicGraph d).Walk v u :=
          SimpleGraph.Walk.cons huv.symm SimpleGraph.Walk.nil
        have hfdel : (⟨s(u, v), hz⟩ : CubicEdge d) ∈ ω \ {e} := by
          exact ⟨hfω, by simpa using hfe⟩
        have hstepopen : walkIsOpen (ω \ {e}) step := by
          intro g hg
          simp only [step, SimpleGraph.Walk.edges_cons,
            SimpleGraph.Walk.edges_nil, List.mem_singleton] at hg
          subst g
          simpa [edgeOpen, Sym2.eq_swap] using hfdel
        have happopen := walkIsOpen_append hqopen hstepopen
        have happsub : walkEdgeFinset (q.append step) ⊆
            (cubicMetricBallEdges d x n).erase e := by
          intro g hg
          rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
            List.mem_append] at hg
          rcases hg with hg | hg
          · exact hqsub ((mem_walkEdgeFinset_iff q g).mpr hg)
          · have hgf : g = ⟨s(u, v), hz⟩ := by
              apply Subtype.ext
              simpa [step, Sym2.eq_swap] using hg
            subst g
            apply Finset.mem_erase.mpr
            exact ⟨hfe, (mem_radiusDeletedBoundaryEdges_iff.mp hfB).1⟩
        apply huD
        rw [mem_radiusDeletedReachableVertices_iff]
        refine ⟨endpoint_mem_cubicMetricBall_of_edge_mem
          (mem_radiusDeletedBoundaryEdges_iff.mp hfB).1 (by simp), ?_⟩
        exact ⟨q.append step, happopen, happsub⟩

/-- Every vertex of a deleted-open walk from the center belongs to the deleted
reachable set. -/
theorem walk_support_subset_radiusDeletedReachableVertices
    {d n : ℕ} {x y : Cubic d} {ω : EdgeConfiguration d} {e : CubicEdge d}
    (q : (cubicGraph d).Walk x y) (hqopen : walkIsOpen (ω \ {e}) q)
    (hqsub : walkEdgeFinset q ⊆ (cubicMetricBallEdges d x n).erase e) :
    ∀ z ∈ q.support, z ∈ radiusDeletedReachableVertices d x n e ω := by
  classical
  intro z hz
  rw [mem_radiusDeletedReachableVertices_iff]
  have hqBall : walkEdgeFinset q ⊆ cubicMetricBallEdges d x n :=
    hqsub.trans (Finset.erase_subset _ _)
  refine ⟨walk_support_subset_cubicMetricBall_of_edges (by simp) q hqBall z hz, ?_⟩
  let r := q.takeUntil z hz
  refine ⟨r, walkIsOpen_of_edges_subset hqopen (q.edges_takeUntil_subset hz), ?_⟩
  intro f hf
  apply hqsub
  rw [mem_walkEdgeFinset_iff] at hf ⊢
  exact q.edges_takeUntil_subset hz hf

/-- The marked pivotal edge is itself a boundary edge of its deleted
reachable set. -/
theorem cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    cubicEdgeOfDart a ∈
      radiusDeletedBoundaryEdges d x n (cubicEdgeOfDart a) ω := by
  classical
  rw [mem_radiusDeletedBoundaryEdges_iff]
  constructor
  · apply (canonicalRadiusWitness hω).edge_subset
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges]
    exact List.mem_map.mpr ⟨a, (mem_radiusPivotalDarts_iff hω a).mp ha |>.1, by
      simp [cubicEdgeOfDart]⟩
  · change cubicEdgeCrossesFinset
      (radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω)
      ⟨s(a.toProd.1, a.toProd.2), by
        rw [SimpleGraph.mem_edgeSet]
        exact a.adj⟩
    rw [cubicEdgeCrossesFinset_mk _ a.adj]
    exact Or.inl ⟨pivotalDart_fst_mem_radiusDeletedReachableVertices hω ha,
      pivotalDart_snd_not_mem_radiusDeletedReachableVertices hω ha⟩

/-- On a radius configuration, the marked pivotal edge is the unique open
boundary edge of its deleted reachable set. -/
theorem open_mem_radiusDeletedBoundaryEdges_iff_pivotalEdge
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω)
    (f : CubicEdge d) :
    f ∈ radiusDeletedBoundaryEdges d x n (cubicEdgeOfDart a) ω ∧ f ∈ ω ↔
      f = cubicEdgeOfDart a := by
  constructor
  · rintro ⟨hfB, hfω⟩
    exact mem_radiusDeletedBoundaryEdges_of_open_imp_eq hfB hfω
  · rintro rfl
    refine ⟨cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hω ha, ?_⟩
    exact pivotal_open_of_mem_event (isIncreasingEvent_radiusConnectionEvent d x n)
      hω ((mem_radiusPivotalDarts_iff hω a).mp ha).2

/-- Every vertex before a pivotal dart on the canonical witness lies on the
origin side of its deleted cut. -/
theorem canonical_take_pivotalDart_support_subset_deletedReachable
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    let W := canonicalRadiusWitness hω
    let i := W.walk.darts.idxOf a
    ∀ z ∈ (W.walk.take i).support,
      z ∈ radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω := by
  classical
  dsimp only
  let W := canonicalRadiusWitness hω
  let i := W.walk.darts.idxOf a
  have haW := (mem_radiusPivotalDarts_iff hω a).mp ha |>.1
  have hi : i < W.walk.darts.length := List.idxOf_lt_length_iff.2 haW
  have hget : W.walk.darts[i] = a := List.getElem_idxOf hi
  have hopen := walkIsOpen_diff_singleton_take_before_dart W.walk W.isPath W.isOpen hi
  rw [hget] at hopen
  apply walk_support_subset_radiusDeletedReachableVertices (W.walk.take i) hopen
  intro f hf
  apply Finset.mem_erase.mpr
  have hfTake : (f : Sym2 (Cubic d)) ∈ W.walk.edges.take i := by
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_take] at hf
    exact hf
  refine ⟨?_, W.edge_subset ((mem_walkEdgeFinset_iff W.walk f).mpr
    (List.mem_of_mem_take hfTake))⟩
  intro hfa
  have hval : (f : Sym2 (Cubic d)) = a.edge := by
    simpa [cubicEdgeOfDart] using congrArg Subtype.val hfa
  apply dart_edge_not_mem_edges_take W.walk W.isPath.isTrail hi
  simpa [hget] using hval ▸ hfTake

/-- Every vertex strictly after a pivotal dart on the canonical witness lies
outside its deleted reachable set. -/
theorem canonical_drop_after_pivotalDart_support_disjoint_deletedReachable
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    let W := canonicalRadiusWitness hω
    let i := W.walk.darts.idxOf a
    ∀ z ∈ (W.walk.drop (i + 1)).support,
      z ∉ radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω := by
  classical
  dsimp only
  let W := canonicalRadiusWitness hω
  let i := W.walk.darts.idxOf a
  let e := cubicEdgeOfDart a
  have haData := (mem_radiusPivotalDarts_iff hω a).mp ha
  have hi : i < W.walk.darts.length := List.idxOf_lt_length_iff.2 haData.1
  have hget : W.walk.darts[i] = a := List.getElem_idxOf hi
  have htailOpen : walkIsOpen (ω \ {e}) (W.walk.drop (i + 1)) := by
    have h := walkIsOpen_diff_singleton_drop_after_dart W.walk W.isPath W.isOpen hi
    simpa [e, hget] using h
  have htailSub : walkEdgeFinset (W.walk.drop (i + 1)) ⊆
      (cubicMetricBallEdges d x n).erase e := by
    intro f hf
    apply Finset.mem_erase.mpr
    have hfDrop : (f : Sym2 (Cubic d)) ∈ W.walk.edges.drop (i + 1) := by
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_drop] at hf
      exact hf
    refine ⟨?_, W.edge_subset ((mem_walkEdgeFinset_iff W.walk f).mpr
      (List.mem_of_mem_drop hfDrop))⟩
    intro hfe
    have hval : (f : Sym2 (Cubic d)) = a.edge := by
      simpa [e, cubicEdgeOfDart] using congrArg Subtype.val hfe
    apply dart_edge_not_mem_edges_drop_succ W.walk W.isPath.isTrail hi
    simpa [hget] using hval ▸ hfDrop
  intro z hz hzD
  rcases (mem_radiusDeletedReachableVertices_iff.mp hzD).2 with
    ⟨q, hqopen, hqsub⟩
  let r := (W.walk.drop (i + 1)).dropUntil z hz
  have hropen : walkIsOpen (ω \ {e}) r :=
    walkIsOpen_of_isSubwalk htailOpen
      ((W.walk.drop (i + 1)).isSubwalk_dropUntil hz)
  have hrsub : walkEdgeFinset r ⊆ (cubicMetricBallEdges d x n).erase e := by
    intro f hf
    apply htailSub
    rw [mem_walkEdgeFinset_iff] at hf ⊢
    exact ((W.walk.drop (i + 1)).isSubwalk_dropUntil hz).edges_subset hf
  have hclosed : ω \ {e} ∈ radiusConnectionEvent d x n :=
    ⟨W.endpoint, W.sphere_mem, q.append r, walkIsOpen_append hqopen hropen, by
      intro f hf
      rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
        List.mem_append] at hf
      rcases hf with hf | hf
      · exact (Finset.mem_erase.mp (hqsub ((mem_walkEdgeFinset_iff q f).mpr hf))).2
      · exact (Finset.mem_erase.mp (hrsub ((mem_walkEdgeFinset_iff r f).mpr hf))).2⟩
  exact ((isIncreasingEvent_radiusConnectionEvent d x n).isPivotal_iff e ω).mp
    haData.2 |>.2 hclosed

/-- Radius-support edges incident to a prescribed finite vertex set. -/
noncomputable def radiusIncidentEdgesOf
    (d : ℕ) (x : Cubic d) (n : ℕ) (D : Finset (Cubic d)) :
    Finset (CubicEdge d) := by
  classical
  exact (cubicMetricBallEdges d x n).filter fun f ↦
    ∃ y ∈ D, y ∈ (f : Sym2 (Cubic d))

@[simp]
theorem mem_radiusIncidentEdgesOf_iff
    {d n : ℕ} {x : Cubic d} {D : Finset (Cubic d)} {f : CubicEdge d} :
    f ∈ radiusIncidentEdgesOf d x n D ↔
      f ∈ cubicMetricBallEdges d x n ∧
      ∃ y ∈ D, y ∈ (f : Sym2 (Cubic d)) := by
  classical
  simp [radiusIncidentEdgesOf]

/-- Finite exploration support: all radius-support edges incident to the
deleted reachable set. -/
noncomputable def radiusDeletedIncidentEdges
    (d : ℕ) (x : Cubic d) (n : ℕ) (e : CubicEdge d)
    (ω : EdgeConfiguration d) : Finset (CubicEdge d) :=
  radiusIncidentEdgesOf d x n (radiusDeletedReachableVertices d x n e ω)

@[simp]
theorem mem_radiusDeletedIncidentEdges_iff
    {d n : ℕ} {x : Cubic d} {e f : CubicEdge d}
    {ω : EdgeConfiguration d} :
    f ∈ radiusDeletedIncidentEdges d x n e ω ↔
      f ∈ cubicMetricBallEdges d x n ∧
      ∃ y ∈ radiusDeletedReachableVertices d x n e ω,
        y ∈ (f : Sym2 (Cubic d)) := by
  simp [radiusDeletedIncidentEdges]

theorem radiusDeletedBoundaryEdges_subset_incidentEdges
    {d n : ℕ} {x : Cubic d} {e : CubicEdge d}
    {ω : EdgeConfiguration d} :
    radiusDeletedBoundaryEdges d x n e ω ⊆
      radiusDeletedIncidentEdges d x n e ω := by
  classical
  intro f hf
  rcases f with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v =>
      have huv : (cubicGraph d).Adj u v := by
        rw [← SimpleGraph.mem_edgeSet]
        exact hz
      have hf' := mem_radiusDeletedBoundaryEdges_iff.mp hf
      rw [mem_radiusDeletedIncidentEdges_iff]
      refine ⟨hf'.1, ?_⟩
      rw [cubicEdgeCrossesFinset_mk _ huv] at hf'
      rcases hf'.2 with h | h
      · exact ⟨u, h.1, by simp⟩
      · exact ⟨v, h.1, by simp⟩

/-- A pivotal edge is part of the exposed incident support at `a` exactly
when it occurs no later than `a` on the canonical pivotal chain. -/
theorem pivotalDart_mem_deletedIncidentEdges_iff_idxOf_le
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a b : (cubicGraph d).Dart}
    (ha : a ∈ radiusPivotalDarts hω) (hb : b ∈ radiusPivotalDarts hω) :
    cubicEdgeOfDart b ∈
        radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω ↔
      (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
        (canonicalRadiusWitness hω).walk.darts.idxOf a := by
  classical
  let W := canonicalRadiusWitness hω
  let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
  let i := W.walk.darts.idxOf a
  let j := W.walk.darts.idxOf b
  have haW : a ∈ W.walk.darts := (mem_radiusPivotalDarts_iff hω a).mp ha |>.1
  have hbW : b ∈ W.walk.darts := (mem_radiusPivotalDarts_iff hω b).mp hb |>.1
  have hi : i < W.walk.darts.length := List.idxOf_lt_length_iff.2 haW
  have hj : j < W.walk.darts.length := List.idxOf_lt_length_iff.2 hbW
  have haGet : W.walk.darts[i] = a := List.getElem_idxOf hi
  have hbGet : W.walk.darts[j] = b := List.getElem_idxOf hj
  have hbE : cubicEdgeOfDart b ∈ cubicMetricBallEdges d x n := by
    apply W.edge_subset
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges]
    exact List.mem_map.mpr ⟨b, hbW, by simp [cubicEdgeOfDart]⟩
  change cubicEdgeOfDart b ∈
      radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω ↔ j ≤ i
  constructor
  · intro hbInc
    by_contra hji
    have hij : i + 1 ≤ j := by omega
    have hbNotTake : b ∉ W.walk.darts.take (i + 1) := by
      rw [List.mem_take_iff_idxOf_lt hbW]
      change ¬j < i + 1
      omega
    have hbDrop : b ∈ W.walk.darts.drop (i + 1) := by
      have hbAll : b ∈ W.walk.darts.take (i + 1) ++ W.walk.darts.drop (i + 1) := by
        simpa only [List.take_append_drop] using hbW
      exact (List.mem_append.mp hbAll).resolve_left hbNotTake
    have hbTail : b ∈ (W.walk.drop (i + 1)).darts := by
      rwa [SimpleGraph.Walk.darts_drop]
    have hbfstNot : b.toProd.1 ∉ D := by
      apply canonical_drop_after_pivotalDart_support_disjoint_deletedReachable hω ha
      exact (W.walk.drop (i + 1)).dart_fst_mem_support_of_mem_darts hbTail
    have hbsndNot : b.toProd.2 ∉ D := by
      apply canonical_drop_after_pivotalDart_support_disjoint_deletedReachable hω ha
      exact (W.walk.drop (i + 1)).dart_snd_mem_support_of_mem_darts hbTail
    rcases (mem_radiusDeletedIncidentEdges_iff.mp hbInc).2 with ⟨y, hyD, hyb⟩
    have hy : y = b.toProd.1 ∨ y = b.toProd.2 := by
      change y ∈ s(b.toProd.1, b.toProd.2) at hyb
      exact Sym2.mem_iff.mp hyb
    exact hy.elim (fun h ↦ hbfstNot (h ▸ hyD))
      (fun h ↦ hbsndNot (h ▸ hyD))
  · intro hji
    rcases hji.lt_or_eq with hlt | heq
    · have hbTakeDarts : b ∈ (W.walk.take i).darts := by
        rw [SimpleGraph.Walk.darts_take]
        rw [List.mem_take_iff_idxOf_lt hbW]
        exact hlt
      have hbfstD : b.toProd.1 ∈ D := by
        apply canonical_take_pivotalDart_support_subset_deletedReachable hω ha
        exact (W.walk.take i).dart_fst_mem_support_of_mem_darts hbTakeDarts
      rw [mem_radiusDeletedIncidentEdges_iff]
      refine ⟨hbE, b.toProd.1, hbfstD, ?_⟩
      change b.toProd.1 ∈ s(b.toProd.1, b.toProd.2)
      simp
    · have hab : b = a := (List.idxOf_inj hbW).mp heq
      rw [hab]
      exact radiusDeletedBoundaryEdges_subset_incidentEdges
        (cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hω ha)

/-- Deleted clusters are nested in the canonical pivotal order. -/
theorem radiusDeletedReachableVertices_subset_of_pivotalDart_idxOf_le
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a b : (cubicGraph d).Dart}
    (ha : a ∈ radiusPivotalDarts hω) (hb : b ∈ radiusPivotalDarts hω)
    (hba : (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
      (canonicalRadiusWitness hω).walk.darts.idxOf a) :
    radiusDeletedReachableVertices d x n (cubicEdgeOfDart b) ω ⊆
      radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω := by
  classical
  let W := canonicalRadiusWitness hω
  let i := W.walk.darts.idxOf b
  let j := W.walk.darts.idxOf a
  change i ≤ j at hba
  rcases hba.lt_or_eq with hij | hij
  · have haW : a ∈ W.walk.darts := (mem_radiusPivotalDarts_iff hω a).mp ha |>.1
    have hbW : b ∈ W.walk.darts := (mem_radiusPivotalDarts_iff hω b).mp hb |>.1
    have haNotTake : a ∉ W.walk.darts.take (i + 1) := by
      rw [List.mem_take_iff_idxOf_lt haW]
      change ¬j < i + 1
      omega
    have haDrop : a ∈ (W.walk.drop (i + 1)).darts := by
      rw [SimpleGraph.Walk.darts_drop]
      have haAll : a ∈ W.walk.darts.take (i + 1) ++ W.walk.darts.drop (i + 1) := by
        simpa only [List.take_append_drop] using haW
      exact (List.mem_append.mp haAll).resolve_left haNotTake
    have hafstNot : a.toProd.1 ∉
        radiusDeletedReachableVertices d x n (cubicEdgeOfDart b) ω := by
      apply canonical_drop_after_pivotalDart_support_disjoint_deletedReachable hω hb
      exact (W.walk.drop (i + 1)).dart_fst_mem_support_of_mem_darts haDrop
    intro y hy
    have hyData := mem_radiusDeletedReachableVertices_iff.mp hy
    rcases hyData.2 with ⟨q, hqopen, hqsub⟩
    have hqSupport : ∀ z ∈ q.support,
        z ∈ radiusDeletedReachableVertices d x n (cubicEdgeOfDart b) ω :=
      walk_support_subset_radiusDeletedReachableVertices q hqopen hqsub
    have haNotQ : (cubicEdgeOfDart a : Sym2 (Cubic d)) ∉ q.edges := by
      intro haQ
      apply hafstNot
      apply hqSupport a.toProd.1
      apply q.mem_support_of_mem_edges haQ
      change a.toProd.1 ∈ s(a.toProd.1, a.toProd.2)
      simp
    have hqopenA : walkIsOpen (ω \ {cubicEdgeOfDart a}) q := by
      intro f hf
      have hfω := hqopen f hf
      refine ⟨hfω.1, ?_⟩
      intro hfa
      apply haNotQ
      have hval : f = (cubicEdgeOfDart a : Sym2 (Cubic d)) := by
        exact congrArg Subtype.val (by simpa using hfa)
      exact hval ▸ hf
    rw [mem_radiusDeletedReachableVertices_iff]
    refine ⟨hyData.1, q, hqopenA, ?_⟩
    intro f hf
    apply Finset.mem_erase.mpr
    have hfOld := hqsub hf
    refine ⟨?_, (Finset.mem_erase.mp hfOld).2⟩
    intro hfa
    apply haNotQ
    have hval : (f : Sym2 (Cubic d)) = (cubicEdgeOfDart a : Sym2 (Cubic d)) :=
      congrArg Subtype.val hfa
    exact hval ▸ (mem_walkEdgeFinset_iff q f).mp hf
  · have hab : b = a := by
      have hbW := (mem_radiusPivotalDarts_iff hω b).mp hb |>.1
      exact (List.idxOf_inj hbW).mp hij
    simp [hab]

theorem radiusDeletedIncidentEdges_subset_of_pivotalDart_idxOf_le
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a b : (cubicGraph d).Dart}
    (ha : a ∈ radiusPivotalDarts hω) (hb : b ∈ radiusPivotalDarts hω)
    (hba : (canonicalRadiusWitness hω).walk.darts.idxOf b ≤
      (canonicalRadiusWitness hω).walk.darts.idxOf a) :
    radiusDeletedIncidentEdges d x n (cubicEdgeOfDart b) ω ⊆
      radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω := by
  intro f hf
  rw [mem_radiusDeletedIncidentEdges_iff] at hf ⊢
  refine ⟨hf.1, ?_⟩
  rcases hf.2 with ⟨y, hy, hyf⟩
  exact ⟨y, radiusDeletedReachableVertices_subset_of_pivotalDart_idxOf_le
    hω ha hb hba hy, hyf⟩

/-- One deleted-open step from a reachable vertex stays in the deleted
reachable set. -/
theorem adj_mem_radiusDeletedReachableVertices
    {d n : ℕ} {x u v : Cubic d} {ω : EdgeConfiguration d} {e : CubicEdge d}
    (hu : u ∈ radiusDeletedReachableVertices d x n e ω)
    (huv : (cubicGraph d).Adj u v)
    (hfE : (⟨s(u, v), by
      rw [SimpleGraph.mem_edgeSet]
      exact huv⟩ : CubicEdge d) ∈ cubicMetricBallEdges d x n)
    (hfopen : (⟨s(u, v), by
      rw [SimpleGraph.mem_edgeSet]
      exact huv⟩ : CubicEdge d) ∈ ω \ {e}) :
    v ∈ radiusDeletedReachableVertices d x n e ω := by
  classical
  have huConn := (mem_radiusDeletedReachableVertices_iff.mp hu).2
  rcases huConn with ⟨q, hqopen, hqsub⟩
  let step : (cubicGraph d).Walk u v := SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil
  have hstepopen : walkIsOpen (ω \ {e}) step := by
    intro g hg
    simp only [step, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, List.mem_singleton] at hg
    subst g
    simpa [edgeOpen] using hfopen
  rw [mem_radiusDeletedReachableVertices_iff]
  refine ⟨endpoint_mem_cubicMetricBall_of_edge_mem hfE (by simp),
    q.append step, walkIsOpen_append hqopen hstepopen, ?_⟩
  intro g hg
  rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_append,
    List.mem_append] at hg
  rcases hg with hg | hg
  · exact hqsub ((mem_walkEdgeFinset_iff q g).mpr hg)
  · have hgf : g = ⟨s(u, v), by
        rw [SimpleGraph.mem_edgeSet]
        exact huv⟩ := by
      apply Subtype.ext
      simpa [step] using hg
    subst g
    exact Finset.mem_erase.mpr ⟨hfopen.2, hfE⟩

private theorem walk_support_subset_radiusDeleted_of_agree_incident
    {d n : ℕ} {x u y : Cubic d} {ω η : EdgeConfiguration d} {e : CubicEdge d}
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n e ω,
      (f ∈ ω ↔ f ∈ η))
    (hu : u ∈ radiusDeletedReachableVertices d x n e ω)
    (q : (cubicGraph d).Walk u y) (hqopen : walkIsOpen (η \ {e}) q)
    (hqsub : walkEdgeFinset q ⊆ (cubicMetricBallEdges d x n).erase e) :
    ∀ z ∈ q.support, z ∈ radiusDeletedReachableVertices d x n e ω := by
  classical
  induction q with
  | nil => simpa using hu
  | @cons u v y huv q ih =>
      let f : CubicEdge d := ⟨s(u, v), by
        rw [SimpleGraph.mem_edgeSet]
        exact huv⟩
      have hfWalk : f ∈ walkEdgeFinset (SimpleGraph.Walk.cons huv q) := by
        rw [mem_walkEdgeFinset_iff]
        simp [f]
      have hfErase := hqsub hfWalk
      have hfE : f ∈ cubicMetricBallEdges d x n := (Finset.mem_erase.mp hfErase).2
      have hfInc : f ∈ radiusDeletedIncidentEdges d x n e ω := by
        rw [mem_radiusDeletedIncidentEdges_iff]
        exact ⟨hfE, u, hu, by simp [f]⟩
      have hfη : f ∈ η \ {e} := by
        have hfirst := hqopen s(u, v) (by simp)
        simpa [f, edgeOpen] using hfirst
      have hfω : f ∈ ω \ {e} := ⟨(hagree f hfInc).mpr hfη.1, hfη.2⟩
      have hv : v ∈ radiusDeletedReachableVertices d x n e ω := by
        apply adj_mem_radiusDeletedReachableVertices hu huv hfE
        simpa [f] using hfω
      have hqopenTail : walkIsOpen (η \ {e}) q :=
        walkIsOpen_of_edges_subset hqopen (by
          intro g hg
          simp [hg])
      have hqsubTail : walkEdgeFinset q ⊆
          (cubicMetricBallEdges d x n).erase e := by
        intro g hg
        apply hqsub
        rw [mem_walkEdgeFinset_iff] at hg ⊢
        simp [hg]
      have htail := ih hv hqopenTail hqsubTail
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      exact hz.elim (fun h ↦ h ▸ hu) (htail z)

/-- Agreement on the explored incident coordinates preserves the entire
deleted reachable set.  This is the cylinder-stability statement needed to
condition on Grimmett's finite marked graph `Γ`. -/
theorem radiusDeletedReachableVertices_eq_of_agree_incident
    {d n : ℕ} {x : Cubic d} {ω η : EdgeConfiguration d} {e : CubicEdge d}
    (hagree : ∀ f ∈ radiusDeletedIncidentEdges d x n e ω,
      (f ∈ ω ↔ f ∈ η)) :
    radiusDeletedReachableVertices d x n e ω =
      radiusDeletedReachableVertices d x n e η := by
  classical
  let D := radiusDeletedReachableVertices d x n e ω
  apply Finset.Subset.antisymm
  · intro y hy
    have hyConn := (mem_radiusDeletedReachableVertices_iff.mp hy).2
    rcases hyConn with ⟨q, hqopen, hqsub⟩
    have hsupport : ∀ z ∈ q.support, z ∈ D := by
      intro z hz
      exact walk_support_subset_radiusDeletedReachableVertices q hqopen hqsub z hz
    have hqopen' : walkIsOpen (η \ {e}) q := by
      intro g hg
      let f : CubicEdge d := ⟨g, q.edges_subset_edgeSet hg⟩
      have hfE : f ∈ cubicMetricBallEdges d x n :=
        (Finset.mem_erase.mp (hqsub ((mem_walkEdgeFinset_iff q f).mpr hg))).2
      have hfInc : f ∈ radiusDeletedIncidentEdges d x n e ω := by
        rw [mem_radiusDeletedIncidentEdges_iff]
        refine ⟨hfE, g.out.1, ?_, Sym2.out_fst_mem g⟩
        exact hsupport g.out.1 (q.mem_support_of_mem_edges hg (Sym2.out_fst_mem g))
      have hfω : f ∈ ω \ {e} := hqopen g hg
      exact ⟨(hagree f hfInc).mp hfω.1, hfω.2⟩
    rw [mem_radiusDeletedReachableVertices_iff]
    exact ⟨(mem_radiusDeletedReachableVertices_iff.mp hy).1, q, hqopen', hqsub⟩
  · intro y hy
    have hyConn := (mem_radiusDeletedReachableVertices_iff.mp hy).2
    rcases hyConn with ⟨q, hqopen, hqsub⟩
    exact walk_support_subset_radiusDeleted_of_agree_incident hagree
      (center_mem_radiusDeletedReachableVertices d n x e ω) q hqopen hqsub y (by simp)

end Percolation

#print axioms Percolation.radiusDeletedReachableVertices_eq_of_agree_incident
