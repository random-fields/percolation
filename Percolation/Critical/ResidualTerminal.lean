import Percolation.Critical.PivotalConditioning

/-!
# Terminal-graph Menger argument after a pivotal exploration

This file generalizes the terminal projection used for the first sausage to
an arbitrary source vertex inside the ambient metric ball.  It is used on the
unexplored exterior of Grimmett's marked graph `Γ`.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

/-- The local radius event restricted to the unexposed exterior edge set.
This is the event to which BK is applied after conditioning on a pivotal
exploration cylinder. -/
def residualLocalRadiusEvent (d : ℕ) (x : Cubic d) (n : ℕ)
    (D : Finset (Cubic d)) (y : Cubic d) (m : ℕ) :
    Set (EdgeConfiguration d) :=
  connectionEventOff d
    (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D)
    ∅ y (cubicMetricSphere d y m)

theorem isIncreasingEvent_residualLocalRadiusEvent
    (d : ℕ) (x : Cubic d) (n : ℕ) (D : Finset (Cubic d))
    (y : Cubic d) (m : ℕ) :
    IsIncreasingEvent (residualLocalRadiusEvent d x n D y m) :=
  isIncreasingEvent_connectionEventOff d _ ∅ y (cubicMetricSphere d y m)

theorem dependsOn_residualLocalRadiusEvent
    (d : ℕ) (x : Cubic d) (n : ℕ) (D : Finset (Cubic d))
    (y : Cubic d) (m : ℕ) :
    DependsOn (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D)
      (residualLocalRadiusEvent d x n D y m) :=
  dependsOn_connectionEventOff d _ ∅ y (cubicMetricSphere d y m)

theorem mem_residualLocalRadiusEvent_of_mem_radiusConnectionEvent
    {d n m : ℕ} {x y : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hη : η ∈ radiusConnectionEvent d y m)
    (hηE : ∀ e : CubicEdge d, e ∈ η →
      e ∈ cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) :
    η ∈ residualLocalRadiusEvent d x n D y m := by
  rcases mem_radiusConnectionEvent_iff_exists_connection.mp hη with
    ⟨z, hz, q, hqopen⟩
  refine ⟨z, hz, q, hqopen, ?_, by simp⟩
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  exact hηE e (hqopen e.1 he)

theorem bernoulliBondMeasure_real_residualLocalRadiusEvent_le
    {d n m : ℕ} {x y : Cubic d} (p : I) (D : Finset (Cubic d)) :
    (bernoulliBondMeasure d p).real (residualLocalRadiusEvent d x n D y m) ≤
      radiusTail d p m :=
  bernoulliBondMeasure_real_connectionEventOff_sphere_le p _ ∅ y

private theorem filter_drop_succ_idxOf
    { α : Type* } [DecidableEq α] (P : α → Bool) (l : List α)
    {a : α} (ha : a ∈ l) (hPa : P a = true) :
    (l.drop (l.idxOf a + 1)).filter P =
      (l.filter P).drop ((l.filter P).idxOf a + 1) := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
      by_cases hca : c = a
      · subst c
        simp [hPa]
      · have haL : a ∈ l := (List.mem_cons.mp ha).resolve_left fun h ↦ hca h.symm
        by_cases hc : P c = true
        · simpa [hca, hc] using ih haL
        · have hc' : P c = false := Bool.eq_false_of_not_eq_true hc
          simpa [hca, hc'] using ih haL

/-- Restrict a configuration to a prescribed finite edge set. -/
def openOnFiniteEdges {d : ℕ} (E : Finset (CubicEdge d))
    (ω : EdgeConfiguration d) : EdgeConfiguration d :=
  (E : Set (CubicEdge d)) ∩ ω

@[simp]
theorem mem_openOnFiniteEdges {d : ℕ} {E : Finset (CubicEdge d)}
    {ω : EdgeConfiguration d} {e : CubicEdge d} :
    e ∈ openOnFiniteEdges E ω ↔ e ∈ E ∧ e ∈ ω :=
  Iff.rfl

private theorem walkFirstRadiusHit_exists {d m : ℕ} {y v : Cubic d}
    (q : (cubicGraph d).Walk y v) (hm : m ≤ cubicL1Dist y v) :
    ∃ k : ℕ, k ≤ q.length ∧ m ≤ cubicL1Dist y (q.getVert k) :=
  ⟨q.length, le_rfl, by simpa using hm⟩

/-- First index at which a walk reaches L¹ distance at least `m` from its
starting point. -/
noncomputable def walkFirstRadiusHitIndex {d m : ℕ} {y v : Cubic d}
    (q : (cubicGraph d).Walk y v) (hm : m ≤ cubicL1Dist y v) : ℕ :=
  Nat.find (walkFirstRadiusHit_exists q hm)

theorem walkFirstRadiusHitIndex_spec {d m : ℕ} {y v : Cubic d}
    (q : (cubicGraph d).Walk y v) (hm : m ≤ cubicL1Dist y v) :
    walkFirstRadiusHitIndex q hm ≤ q.length ∧
      m ≤ cubicL1Dist y (q.getVert (walkFirstRadiusHitIndex q hm)) :=
  Nat.find_spec (walkFirstRadiusHit_exists q hm)

theorem walkFirstRadiusHit_dist_eq {d m : ℕ} {y v : Cubic d}
    (q : (cubicGraph d).Walk y v) (hm : m ≤ cubicL1Dist y v) :
    cubicL1Dist y (q.getVert (walkFirstRadiusHitIndex q hm)) = m := by
  let k := walkFirstRadiusHitIndex q hm
  have hk := walkFirstRadiusHitIndex_spec q hm
  change cubicL1Dist y (q.getVert k) = m
  change k ≤ q.length ∧ m ≤ cubicL1Dist y (q.getVert k) at hk
  by_cases hkzero : k = 0
  · have hmzero : m = 0 := by simpa [k, hkzero] using hk.2
    simp [k, hkzero, hmzero]
  · let j := k - 1
    have hksucc : k = j + 1 := by omega
    have hjlt : cubicL1Dist y (q.getVert j) < m := by
      apply lt_of_not_ge
      intro hj
      exact Nat.find_min (walkFirstRadiusHit_exists q hm)
        (show j < k by omega) ⟨by omega, hj⟩
    have hjlen : j < q.length := by omega
    have hadj := q.adj_getVert_succ hjlen
    rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
    have hupper : cubicL1Dist y (q.getVert (j + 1)) ≤ m := by
      calc
        cubicL1Dist y (q.getVert (j + 1)) ≤
            cubicL1Dist y (q.getVert j) +
              cubicL1Dist (q.getVert j) (q.getVert (j + 1)) :=
          cubicL1Dist_triangle _ _ _
        _ = cubicL1Dist y (q.getVert j) + 1 := by
          rw [ha, cubicL1Dist_stepFrom]
        _ ≤ m := by omega
    rw [hksucc]
    exact le_antisymm hupper (by simpa [hksucc] using hk.2)

theorem walkFirstRadiusHit_dart_fst_dist_lt {d m : ℕ} {y v : Cubic d}
    (q : (cubicGraph d).Walk y v) (hm : m ≤ cubicL1Dist y v)
    {a : (cubicGraph d).Dart}
    (ha : a ∈ (q.take (walkFirstRadiusHitIndex q hm)).darts) :
    cubicL1Dist y a.toProd.1 < m := by
  let k := walkFirstRadiusHitIndex q hm
  have hk := walkFirstRadiusHitIndex_spec q hm
  rw [SimpleGraph.Walk.darts_take] at ha
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  have hik : i < k := by
    simpa [List.length_take, Nat.min_eq_left hk.1] using hi
  have hiq : i < q.darts.length := by simpa using lt_of_lt_of_le hik hk.1
  have hget := q.darts_getElem_eq_getVert i hiq
  have hia' : q.darts[i] = a := by rw [← hia]; simp
  have hfst : a.toProd.1 = q.getVert i := by
    rw [← hia', hget]
  rw [hfst]
  apply lt_of_not_ge
  intro hge
  exact Nat.find_min (walkFirstRadiusHit_exists q hm) hik ⟨by omega, hge⟩

theorem walkFirstRadiusHitIndex_eq_length_of_getVert_eq_end
    {d m : ℕ} {y v : Cubic d} (q : (cubicGraph d).Walk y v)
    (hqPath : q.IsPath) (hm : m ≤ cubicL1Dist y v)
    (hend : q.getVert (walkFirstRadiusHitIndex q hm) = v) :
    walkFirstRadiusHitIndex q hm = q.length := by
  let K := walkFirstRadiusHitIndex q hm
  have hK := walkFirstRadiusHitIndex_spec q hm |>.1
  let i : Fin q.support.length := ⟨K, by simpa [q.length_support] using Nat.lt_add_one_of_le hK⟩
  let j : Fin q.support.length := ⟨q.length, by simp [q.length_support]⟩
  have hij : i = j := hqPath.support_nodup.injective_get (by
    simpa [i, j, q.support_getElem_eq_getVert] using hend.trans q.getVert_length.symm)
  exact congrArg Fin.val hij

noncomputable def pivotalTailWalk
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    (cubicGraph d).Walk a.toProd.2 (canonicalRadiusWitness hω).endpoint :=
  canonicalTailWalkAfterDart hω ((mem_radiusPivotalDarts_iff hω a).mp ha).1

theorem pivotalTailWalk_darts
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    (pivotalTailWalk hω ha).darts =
      (canonicalRadiusWitness hω).walk.darts.drop
        ((canonicalRadiusWitness hω).walk.darts.idxOf a + 1) := by
  exact canonicalTailWalkAfterDart_darts hω _

theorem pivotalTailWalk_edges
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    (pivotalTailWalk hω ha).edges =
      (canonicalRadiusWitness hω).walk.edges.drop
        ((canonicalRadiusWitness hω).walk.darts.idxOf a + 1) := by
  exact canonicalTailWalkAfterDart_edges hω _

theorem pivotalTailWalk_isPath
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    (pivotalTailWalk hω ha).IsPath :=
  canonicalTailWalkAfterDart_isPath hω _

theorem pivotalTailWalk_support_outside_deletedReachable
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    ∀ z ∈ (pivotalTailWalk hω ha).support,
      z ∉ radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω := by
  intro z hz
  apply canonical_drop_after_pivotalDart_support_disjoint_deletedReachable hω ha
  have hs := canonicalTailWalkAfterDart_support hω
    ((mem_radiusPivotalDarts_iff hω _).mp ha).1
  rw [← hs]
  exact hz

theorem pivotalTailWalk_edgeFinset_subset_exterior
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    walkEdgeFinset (pivotalTailWalk hω ha) ⊆
      cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n
        (radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω) := by
  classical
  intro f hf
  let q := pivotalTailWalk hω ha
  have hfq : (f : Sym2 (Cubic d)) ∈ q.edges := (mem_walkEdgeFinset_iff q f).mp hf
  have hfW : (f : Sym2 (Cubic d)) ∈ (canonicalRadiusWitness hω).walk.edges := by
    change (f : Sym2 (Cubic d)) ∈ (pivotalTailWalk hω ha).edges at hfq
    rw [pivotalTailWalk_edges] at hfq
    exact List.mem_of_mem_drop hfq
  apply Finset.mem_sdiff.mpr
  refine ⟨(canonicalRadiusWitness hω).edge_subset
    ((mem_walkEdgeFinset_iff _ f).mpr hfW), ?_⟩
  intro hfInc
  rcases (mem_radiusIncidentEdgesOf_iff.mp hfInc).2 with ⟨z, hzD, hzf⟩
  apply pivotalTailWalk_support_outside_deletedReachable hω ha z
  · exact q.mem_support_of_mem_edges hfq hzf
  · exact hzD

theorem pivotalTailWalk_isOpen_openOnExterior
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω) :
    walkIsOpen
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n
          (radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω)) ω)
      (pivotalTailWalk hω ha) := by
  intro g hg
  let f : CubicEdge d := ⟨g, (pivotalTailWalk hω ha).edges_subset_edgeSet hg⟩
  refine ⟨pivotalTailWalk_edgeFinset_subset_exterior hω ha
    ((mem_walkEdgeFinset_iff _ f).mpr hg), ?_⟩
  have hfW : g ∈ (canonicalRadiusWitness hω).walk.edges := by
    rw [pivotalTailWalk_edges] at hg
    exact List.mem_of_mem_drop hg
  exact (canonicalRadiusWitness hω).isOpen g hfW

/-- If a later pivotal dart occurs before the first radius-`m` hit after the
marked pivot, then the next sausage gap is strictly smaller than `m`. -/
theorem nextSausageGap_lt_of_pivotalDart_mem_tail_firstHit
    {d n m : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {a b : (cubicGraph d).Dart}
    (ha : a ∈ radiusPivotalDarts hω) (hb : b ∈ radiusPivotalDarts hω)
    (hm : m ≤ cubicL1Dist a.toProd.2 (canonicalRadiusWitness hω).endpoint)
    (hbHit : b ∈ ((pivotalTailWalk hω ha).take
      (walkFirstRadiusHitIndex (pivotalTailWalk hω ha) hm)).darts) :
    sausageGap d x n ω ((radiusPivotalDarts hω).idxOf a + 2) < m := by
  classical
  let W := canonicalRadiusWitness hω
  let i := W.walk.darts.idxOf a
  let q := pivotalTailWalk hω ha
  let K := walkFirstRadiusHitIndex q hm
  let P := fun c : (cubicGraph d).Dart ↦
    decide (IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart c) ω)
  let L := radiusPivotalDarts hω
  let j := L.idxOf a
  have haData := (mem_radiusPivotalDarts_iff hω a).mp ha
  have hbData := (mem_radiusPivotalDarts_iff hω b).mp hb
  have hPa : P a = true := by simp [P, haData.2]
  have hPb : P b = true := by simp [P, hbData.2]
  have hbRaw : b ∈ (W.walk.darts.drop (i + 1)).take K := by
    simpa [q, K, i, W, SimpleGraph.Walk.darts_take,
      pivotalTailWalk_darts] using hbHit
  obtain ⟨c, t, hfilter, hcRaw⟩ := exists_head_filter_mem_take P hbRaw hPb
  have hdrop := filter_drop_succ_idxOf P W.walk.darts haData.1 hPa
  have hLdrop : L.drop (j + 1) = c :: t := by
    calc
      L.drop (j + 1) = (W.walk.darts.drop (i + 1)).filter P := by
        simpa [L, j, i, radiusPivotalDarts, P] using hdrop.symm
      _ = c :: t := hfilter
  have hnext : L[j + 1]? = some c := by
    have hhead := congrArg (fun r : List ((cubicGraph d).Dart) ↦ r[0]?) hLdrop
    simpa [List.getElem?_drop] using hhead
  have hprev : L[j]? = some a := by
    simpa [j] using List.getElem?_idxOf ha
  have hcHit : c ∈ (q.take K).darts := by
    simpa [q, K, i, SimpleGraph.Walk.darts_take,
      pivotalTailWalk_darts] using hcRaw
  have hdist : cubicL1Dist a.toProd.2 c.toProd.1 < m := by
    simpa [q] using walkFirstRadiusHit_dart_fst_dist_lt q hm hcHit
  unfold sausageGap
  simp only [hω, ↓reduceDIte]
  change sausageGapOfList x n L (j + 2) < m
  simpa [sausageGapOfList, hnext, hprev] using hdist

theorem sausageGap_succ_succ_eq_pivotalDart_dist
    {d n k : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    (hk : k + 1 < (radiusPivotalDarts hω).length) :
    sausageGap d x n ω (k + 2) =
      cubicL1Dist ((radiusPivotalDarts hω)[k].toProd.2)
        ((radiusPivotalDarts hω)[k + 1].toProd.1) := by
  unfold sausageGap
  simp only [hω, ↓reduceDIte]
  simp only [sausageGapOfList]
  have hk0 : k < (radiusPivotalDarts hω).length := by omega
  have hprev : (radiusPivotalDarts hω)[k]? =
      some ((radiusPivotalDarts hω)[k]) := List.getElem?_eq_getElem hk0
  have hcur : (radiusPivotalDarts hω)[k + 1]? =
      some ((radiusPivotalDarts hω)[k + 1]) := List.getElem?_eq_getElem hk
  rw [hprev, hcur]

/-- The marked far endpoint is no farther from the origin than the sum of all
preceding sausage gaps plus one unit for each pivotal edge. -/
theorem pivotalDart_endpoint_dist_le_sum_gaps
    {d n k : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    (hk : k < (radiusPivotalDarts hω).length) :
    cubicL1Dist x ((radiusPivotalDarts hω)[k].toProd.2) ≤
      (∑ i : Fin (k + 1), sausageGap d x n ω (i + 1)) + (k + 1) := by
  induction k with
  | zero =>
      have hLpos : 0 < (radiusPivotalDarts hω).length := by omega
      let a := (radiusPivotalDarts hω)[0]
      have hgap := sausageGap_one_eq_firstPivotalDist hω hLpos
      have hadj : cubicL1Dist a.toProd.1 a.toProd.2 = 1 := by
        rw [← cubicGraph_dist_eq_l1Dist, SimpleGraph.dist_eq_one_iff_adj]
        exact a.adj
      rw [Fin.sum_univ_one]
      change cubicL1Dist x a.toProd.2 ≤ sausageGap d x n ω 1 + 1
      calc
        cubicL1Dist x a.toProd.2 ≤
            cubicL1Dist x a.toProd.1 + cubicL1Dist a.toProd.1 a.toProd.2 :=
          cubicL1Dist_triangle _ _ _
        _ = sausageGap d x n ω 1 + 1 := by rw [hgap, hadj]
  | succ k ih =>
      have hkPrev : k < (radiusPivotalDarts hω).length := by omega
      have hprev := ih hkPrev
      let a := (radiusPivotalDarts hω)[k]
      let b := (radiusPivotalDarts hω)[k + 1]
      have hgap := sausageGap_succ_succ_eq_pivotalDart_dist hω hk
      change sausageGap d x n ω (k + 2) =
        cubicL1Dist a.toProd.2 b.toProd.1 at hgap
      change cubicL1Dist x a.toProd.2 ≤
        (∑ i : Fin (k + 1), sausageGap d x n ω (i + 1)) + (k + 1) at hprev
      have hadj : cubicL1Dist b.toProd.1 b.toProd.2 = 1 := by
        rw [← cubicGraph_dist_eq_l1Dist, SimpleGraph.dist_eq_one_iff_adj]
        exact b.adj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      change cubicL1Dist x b.toProd.2 ≤
        ((∑ i : Fin (k + 1), sausageGap d x n ω (i + 1)) +
          sausageGap d x n ω (k + 2)) + (k + 2)
      calc
        cubicL1Dist x b.toProd.2 ≤
            cubicL1Dist x b.toProd.1 + cubicL1Dist b.toProd.1 b.toProd.2 :=
          cubicL1Dist_triangle _ _ _
        _ ≤ (cubicL1Dist x a.toProd.2 +
              cubicL1Dist a.toProd.2 b.toProd.1) +
                cubicL1Dist b.toProd.1 b.toProd.2 :=
          Nat.add_le_add_right (cubicL1Dist_triangle _ _ _) _
        _ ≤ ((∑ i : Fin (k + 1), sausageGap d x n ω (i + 1)) +
              sausageGap d x n ω (k + 2)) + (k + 2) := by
          rw [← hgap, hadj]
          omega

theorem markedPivotalDart_endpoint_dist_le_prefixSum
    {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hω : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω.1)
    (hmark : (radiusPivotalDarts hω.1).idxOf a + 1 = rs.length) :
    cubicL1Dist x a.toProd.2 ≤ rs.sum + rs.length := by
  classical
  let L := radiusPivotalDarts hω.1
  let k := L.idxOf a
  have hk : k < L.length := List.idxOf_lt_length_iff.2 ha
  have hbound := pivotalDart_endpoint_dist_le_sum_gaps hω.1 hk
  have hget : L[k] = a := List.getElem_idxOf hk
  have hsum : (∑ i : Fin rs.length, sausageGap d x n ω (i + 1)) = rs.sum := by
    calc
      (∑ i : Fin rs.length, sausageGap d x n ω (i + 1)) =
          ∑ i : Fin rs.length, rs.get i := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hω.2 i i.isLt
      _ = (List.ofFn rs.get).sum :=
        (List.sum_ofFn (n := rs.length) (f := rs.get)).symm
      _ = rs.sum := congrArg List.sum (List.ofFn_get rs)
  change cubicL1Dist x L[k].toProd.2 ≤ _ at hbound
  rw [hget] at hbound
  have hsum' : (∑ i : Fin (k + 1), sausageGap d x n ω (i + 1)) = rs.sum := by
    rw [hmark]
    exact hsum
  calc
    cubicL1Dist x a.toProd.2 ≤
        (∑ i : Fin (k + 1), sausageGap d x n ω (i + 1)) + (k + 1) := hbound
    _ = rs.sum + rs.length := by rw [hsum', hmark]

theorem markedPivotalDart_outerSphere_dist_ge
    {d n r : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hω : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω.1)
    (hmark : (radiusPivotalDarts hω.1).idxOf a + 1 = rs.length)
    (hbudget : rs.sum + r + (rs.length + 1) ≤ n)
    {v : Cubic d} (hv : v ∈ cubicMetricSphere d x n) :
    r + 1 ≤ cubicL1Dist a.toProd.2 v := by
  have haDist := markedPivotalDart_endpoint_dist_le_prefixSum hω ha hmark
  have htri := cubicL1Dist_triangle x a.toProd.2 v
  have hvDist := mem_cubicMetricSphere_iff_l1Dist_eq.mp hv
  omega

theorem markedPivotalDart_outerSphere_dist_gt
    {d n r : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hω : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hω.1)
    (hmark : (radiusPivotalDarts hω.1).idxOf a + 1 = rs.length)
    (hbudget : rs.sum + r + (rs.length + 1) < n)
    {v : Cubic d} (hv : v ∈ cubicMetricSphere d x n) :
    r + 1 < cubicL1Dist a.toProd.2 v := by
  have haDist := markedPivotalDart_endpoint_dist_le_prefixSum hω ha hmark
  have htri := cubicL1Dist_triangle x a.toProd.2 v
  have hvDist := mem_cubicMetricSphere_iff_l1Dist_eq.mp hv
  omega

/-- Project a source-to-terminal path in `radiusTerminalGraph` from an
arbitrary ball vertex, rather than only from the centre. -/
structure RadiusTerminalProjectionFrom {d n : ℕ} {x : Cubic d}
    (ξ : EdgeConfiguration d)
    (source z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (shortcut : Prop)
    (p : (radiusTerminalGraph ξ z shortcut).Walk (some source) none) where
  endpoint : {y : Cubic d // y ∈ cubicMetricBall d x n}
  terminal_kind : endpoint.1 ∈ cubicMetricSphere d x n ∨ (shortcut ∧ endpoint = z)
  walk : (radiusOpenBallGraph ξ).Walk source endpoint
  edge_subset : ∀ e ∈ walk.edges, Sym2.map some e ∈ p.edges
  last_edge_mem : s(some endpoint, none) ∈ p.edges

noncomputable def radiusTerminalProjectionFromOfPath
    {d n : ℕ} {x : Cubic d} {ξ : EdgeConfiguration d}
    {source z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop}
    (p : (radiusTerminalGraph ξ z shortcut).Walk (some source) none)
    (hp : p.IsPath) : RadiusTerminalProjectionFrom ξ source z shortcut p := by
  have hnil : ¬p.Nil := by
    intro h
    exact Option.some_ne_none source h.eq
  have hadj := p.adj_penultimate hnil
  cases hpen : p.penultimate with
  | none => exact (hadj.ne (by simp [hpen])).elim
  | some u =>
      let r : (radiusTerminalGraph ξ z shortcut).Walk (some source) (some u) :=
        p.dropLast.copy rfl hpen
      have hnodup : (p.dropLast.support ++ [none]).Nodup := by
        rw [p.support_dropLast_concat hnil]
        exact hp.support_nodup
      have hnoneDrop : none ∉ p.dropLast.support := by
        have h := (List.nodup_append.mp hnodup).2.2
        exact fun hmem ↦ h none hmem none (by simp) rfl
      have hnone : none ∉ r.support := by simpa [r] using hnoneDrop
      let q := projectRadiusTerminalWalk r hnone
      refine ⟨u, ?_, q, ?_, ?_⟩
      · apply radiusTerminalGraph_adj_sink_iff.mp
        simpa [hpen] using hadj
      · intro e heq
        have heR : Sym2.map some e ∈ r.edges := by
          rw [← map_projectRadiusTerminalWalk_edges r hnone]
          exact List.mem_map.mpr ⟨e, heq, rfl⟩
        have heDrop : Sym2.map some e ∈ p.dropLast.edges := by simpa [r] using heR
        exact (SimpleGraph.Walk.isSubwalk_take p (p.length - 1)).edges_subset heDrop
      · simpa [hpen] using p.mk_penultimate_end_mem_edges hnil

noncomputable def RadiusTerminalProjectionFrom.cubicWalk
    {d n : ℕ} {x : Cubic d} {ξ : EdgeConfiguration d}
    {source z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop}
    {p : (radiusTerminalGraph ξ z shortcut).Walk (some source) none}
    (P : RadiusTerminalProjectionFrom ξ source z shortcut p) :
    (cubicGraph d).Walk source.1 P.endpoint.1 :=
  P.walk.map (radiusOpenBallToCubicHom ξ)

noncomputable def RadiusTerminalProjectionFrom.edgeFinset
    {d n : ℕ} {x : Cubic d} {ξ : EdgeConfiguration d}
    {source z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop}
    {p : (radiusTerminalGraph ξ z shortcut).Walk (some source) none}
    (P : RadiusTerminalProjectionFrom ξ source z shortcut p) : Finset (CubicEdge d) :=
  walkEdgeFinset P.cubicWalk

theorem RadiusTerminalProjectionFrom.edgeFinset_subset
    {d n : ℕ} {x : Cubic d} {ξ : EdgeConfiguration d}
    {source z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop}
    {p : (radiusTerminalGraph ξ z shortcut).Walk (some source) none}
    (P : RadiusTerminalProjectionFrom ξ source z shortcut p) :
    (P.edgeFinset : Set (CubicEdge d)) ⊆ ξ := by
  intro e he
  have he' : (e : Sym2 (Cubic d)) ∈ P.cubicWalk.edges :=
    (mem_walkEdgeFinset_iff P.cubicWalk e).mp he
  exact walkIsOpen_map_radiusOpenBallToCubicHom P.walk e.1 he'

theorem radiusTerminalProjectionFrom_edgeFinset_disjoint
    {d n : ℕ} {x : Cubic d} {ξ : EdgeConfiguration d}
    {source z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop}
    {p q : (radiusTerminalGraph ξ z shortcut).Walk (some source) none}
    (P : RadiusTerminalProjectionFrom ξ source z shortcut p)
    (Q : RadiusTerminalProjectionFrom ξ source z shortcut q)
    (hpq : p.edges.Disjoint q.edges) : Disjoint P.edgeFinset Q.edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heP heQ
  have hePc : (e : Sym2 (Cubic d)) ∈ P.cubicWalk.edges :=
    (mem_walkEdgeFinset_iff P.cubicWalk e).mp heP
  have heQc : (e : Sym2 (Cubic d)) ∈ Q.cubicWalk.edges :=
    (mem_walkEdgeFinset_iff Q.cubicWalk e).mp heQ
  change (e : Sym2 (Cubic d)) ∈
    (P.walk.map (radiusOpenBallToCubicHom ξ)).edges at hePc
  change (e : Sym2 (Cubic d)) ∈
    (Q.walk.map (radiusOpenBallToCubicHom ξ)).edges at heQc
  rw [SimpleGraph.Walk.edges_map] at hePc heQc
  obtain ⟨f, hfP, hfeP⟩ := List.mem_map.mp hePc
  obtain ⟨g, hgQ, hgeQ⟩ := List.mem_map.mp heQc
  have hfg : f = g := by
    apply Sym2.map.injective Subtype.val_injective
    exact hfeP.trans hgeQ.symm
  subst g
  exact List.disjoint_left.mp hpq (P.edge_subset f hfP) (Q.edge_subset f hgQ)

/-- Lift an arbitrary open ball-contained walk from `source` to the outer
sphere into the terminal graph. -/
noncomputable def radiusTerminalFullWalkFrom
    {d n : ℕ} {x : Cubic d} {ξ : EdgeConfiguration d}
    (source z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    {v : Cubic d} (hv : v ∈ cubicMetricSphere d x n)
    (q : (cubicGraph d).Walk source.1 v) (hqopen : walkIsOpen ξ q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n) :
    (radiusTerminalGraph ξ z True).Walk (some source) none := by
  let Q := radiusOpenBallWalkLiftOf source.2
    (cubicMetricSphere_subset_ball d x n hv) q hqopen hqball
  exact (Q.walk.map (radiusOpenBallToTerminalHom ξ z True)).concat
    (radiusTerminalGraph_adj_sink_iff.mpr (Or.inl hv))

/-- Lift an arbitrary open ball-contained walk from `source` to the marked
local target and then use the artificial shortcut to the terminal. -/
noncomputable def radiusTerminalShortcutWalkFrom
    {d n : ℕ} {x : Cubic d} {ξ : EdgeConfiguration d}
    (source z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (q : (cubicGraph d).Walk source.1 z.1) (hqopen : walkIsOpen ξ q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n) :
    (radiusTerminalGraph ξ z True).Walk (some source) none := by
  let Q := radiusOpenBallWalkLiftOf source.2 z.2 q hqopen hqball
  exact (Q.walk.map (radiusOpenBallToTerminalHom ξ z True)).concat
    (radiusTerminalGraph_adj_sink_iff.mpr (Or.inr ⟨True.intro, rfl⟩))

/-- Every vertex of a walk using only edges outside `radiusIncidentEdgesOf D`
stays outside `D`, provided its starting vertex is outside. -/
theorem walk_support_disjoint_of_edges_subset_not_incident
    {d n : ℕ} {x u v : Cubic d} {D : Finset (Cubic d)}
    (hu : u ∉ D) (q : (cubicGraph d).Walk u v)
    (hqsub : walkEdgeFinset q ⊆
      cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) :
    ∀ z ∈ q.support, z ∉ D := by
  classical
  induction q with
  | nil => simpa using hu
  | @cons u w v huw q ih =>
      let e : CubicEdge d := ⟨s(u, w), by
        rw [SimpleGraph.mem_edgeSet]
        exact huw⟩
      have heWalk : e ∈ walkEdgeFinset (SimpleGraph.Walk.cons huw q) := by
        rw [mem_walkEdgeFinset_iff]
        simp [e]
      have heOutside := Finset.mem_sdiff.mp (hqsub heWalk)
      have hw : w ∉ D := by
        intro hwD
        apply heOutside.2
        rw [mem_radiusIncidentEdgesOf_iff]
        exact ⟨heOutside.1, w, hwD, by simp [e]⟩
      have hqsubTail : walkEdgeFinset q ⊆
          cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D := by
        intro f hf
        apply hqsub
        rw [mem_walkEdgeFinset_iff] at hf ⊢
        simp [hf]
      have htail := ih hw hqsubTail
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      exact hz.elim (fun h ↦ h ▸ hu) (htail z)

theorem mem_disjointOccurrence_of_edgeDisjoint_residual_outerWalks
    {d n m : ℕ} {x y : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n) (hyD : y ∉ D)
    {u v : {w : Cubic d // w ∈ cubicMetricBall d x n}}
    (hu : u.1 ∈ cubicMetricSphere d x n) (hv : v.1 ∈ cubicMetricSphere d x n)
    (hOuterFar : ∀ w ∈ cubicMetricSphere d x n, m ≤ cubicL1Dist y w)
    (p : (radiusOpenBallGraph
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η)).Walk
        ⟨y, hyBall⟩ u)
    (q : (radiusOpenBallGraph
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η)).Walk
        ⟨y, hyBall⟩ v)
    (hpq : p.edges.Disjoint q.edges) :
    η ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D y m)
      (radiusConnectionEventOffExploration d x n D y
        (cubicMetricSphere d x n)) := by
  let ξ := openOnFiniteEdges
    (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η
  let p' := p.map (radiusOpenBallToCubicHom ξ)
  let q' := q.map (radiusOpenBallToCubicHom ξ)
  let H := walkEdgeFinset p'
  let K := walkEdgeFinset q'
  have hHK : Disjoint H K := by
    rw [Finset.disjoint_left]
    intro e heH heK
    have hep : (e : Sym2 (Cubic d)) ∈ p'.edges := (mem_walkEdgeFinset_iff p' e).mp heH
    have heq : (e : Sym2 (Cubic d)) ∈ q'.edges := (mem_walkEdgeFinset_iff q' e).mp heK
    rw [SimpleGraph.Walk.edges_map] at hep heq
    obtain ⟨f, hfp, hfe⟩ := List.mem_map.mp hep
    obtain ⟨g, hgq, hge⟩ := List.mem_map.mp heq
    have hfg : f = g := by
      apply Sym2.map.injective Subtype.val_injective
      exact hfe.trans hge.symm
    subst g
    exact List.disjoint_left.mp hpq hfp hgq
  have hHξ : (H : Set (CubicEdge d)) ⊆ ξ := by
    intro e he
    exact walkIsOpen_map_radiusOpenBallToCubicHom p e.1
      ((mem_walkEdgeFinset_iff p' e).mp he)
  have hKξ : (K : Set (CubicEdge d)) ⊆ ξ := by
    intro e he
    exact walkIsOpen_map_radiusOpenBallToCubicHom q e.1
      ((mem_walkEdgeFinset_iff q' e).mp he)
  have hHη : (H : Set (CubicEdge d)) ⊆ η := fun e he ↦ (hHξ he).2
  have hKη : (K : Set (CubicEdge d)) ⊆ η := fun e he ↦ (hKξ he).2
  have hHE : H ⊆ cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D :=
    fun e he ↦ (hHξ he).1
  have hKE : K ⊆ cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D :=
    fun e he ↦ (hKξ he).1
  have hHradius : (H : Set (CubicEdge d)) ∈ radiusConnectionEvent d y m := by
    apply exists_open_walk_to_cubicMetricSphere_in_ball p'
      (walkIsOpen_walkEdgeFinset p')
    exact hOuterFar u.1 hu
  have hHlocal : (H : Set (CubicEdge d)) ∈
      residualLocalRadiusEvent d x n D y m :=
    mem_residualLocalRadiusEvent_of_mem_radiusConnectionEvent hHradius
      (fun _ he ↦ hHE he)
  have hKoff : (K : Set (CubicEdge d)) ∈
      radiusConnectionEventOffExploration d x n D y (cubicMetricSphere d x n) := by
    refine ⟨v.1, hv, q', walkIsOpen_walkEdgeFinset q', hKE, ?_⟩
    intro w hw
    apply walk_support_disjoint_of_edges_subset_not_incident hyD q' hKE w
    exact List.mem_of_mem_tail hw
  exact ⟨H, K, hHK, hHη, hKη, hHlocal, hKoff⟩

/-- Two edge-disjoint terminal paths give disjoint witnesses for the local
radius event and the residual off-exploration outer connection. -/
theorem mem_disjointOccurrence_of_residual_terminal_paths
    {d n m : ℕ} {x y : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n) (hyD : y ∉ D)
    (z : {v : Cubic d // v ∈ cubicMetricBall d x n})
    (hzLocal : z.1 ∈ cubicMetricSphere d y m)
    (hOuterFar : ∀ v ∈ cubicMetricSphere d x n, m ≤ cubicL1Dist y v)
    {p q : (radiusTerminalGraph
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) z True).Walk
        (some ⟨y, hyBall⟩) none}
    (hp : p.IsPath) (hq : q.IsPath) (hpq : p.edges.Disjoint q.edges) :
    η ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D y m)
      (radiusConnectionEventOffExploration d x n D y
        (cubicMetricSphere d x n)) := by
  classical
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let ξ := openOnFiniteEdges E η
  let source : {v : Cubic d // v ∈ cubicMetricBall d x n} := ⟨y, hyBall⟩
  let P := radiusTerminalProjectionFromOfPath p hp
  let Q := radiusTerminalProjectionFromOfPath q hq
  have hfinDisj : Disjoint P.edgeFinset Q.edgeFinset :=
    radiusTerminalProjectionFrom_edgeFinset_disjoint P Q hpq
  have hPξ : (P.edgeFinset : Set (CubicEdge d)) ⊆ ξ := P.edgeFinset_subset
  have hQξ : (Q.edgeFinset : Set (CubicEdge d)) ⊆ ξ := Q.edgeFinset_subset
  have hPη : (P.edgeFinset : Set (CubicEdge d)) ⊆ η :=
    fun e he ↦ (mem_openOnFiniteEdges.mp (hPξ he)).2
  have hQη : (Q.edgeFinset : Set (CubicEdge d)) ⊆ η :=
    fun e he ↦ (mem_openOnFiniteEdges.mp (hQξ he)).2
  have hPE : P.edgeFinset ⊆ E :=
    fun e he ↦ (mem_openOnFiniteEdges.mp (hPξ he)).1
  have hQE : Q.edgeFinset ⊆ E :=
    fun e he ↦ (mem_openOnFiniteEdges.mp (hQξ he)).1
  have local_of_projection
      {r : (radiusTerminalGraph ξ z True).Walk (some source) none}
      (R : RadiusTerminalProjectionFrom ξ source z True r)
      (hRE : R.edgeFinset ⊆ E) :
      (R.edgeFinset : Set (CubicEdge d)) ∈
        residualLocalRadiusEvent d x n D y m := by
    apply mem_residualLocalRadiusEvent_of_mem_radiusConnectionEvent
    · apply exists_open_walk_to_cubicMetricSphere_in_ball R.cubicWalk
        (walkIsOpen_walkEdgeFinset R.cubicWalk)
      rcases R.terminal_kind with hOuter | ⟨_, hrz⟩
      · exact hOuterFar R.endpoint.1 hOuter
      · rw [hrz]
        exact (mem_cubicMetricSphere_iff_l1Dist_eq.mp hzLocal).ge
    · exact fun _ he ↦ hRE he
  have off_of_projection
      {r : (radiusTerminalGraph ξ z True).Walk (some source) none}
      (R : RadiusTerminalProjectionFrom ξ source z True r)
      (hOuter : R.endpoint.1 ∈ cubicMetricSphere d x n)
      (hRE : R.edgeFinset ⊆ E) :
      (R.edgeFinset : Set (CubicEdge d)) ∈
        radiusConnectionEventOffExploration d x n D y (cubicMetricSphere d x n) := by
    refine ⟨R.endpoint.1, hOuter, R.cubicWalk,
      walkIsOpen_walkEdgeFinset R.cubicWalk, ?_, ?_⟩
    · exact hRE
    · intro v hv
      apply walk_support_disjoint_of_edges_subset_not_incident hyD R.cubicWalk hRE v
      exact List.mem_of_mem_tail hv
  have hnotBothShortcut :
      ¬((True ∧ P.endpoint = z) ∧ (True ∧ Q.endpoint = z)) := by
    rintro ⟨⟨_, hPz⟩, ⟨_, hQz⟩⟩
    have heP : s(some z, none) ∈ p.edges := by simpa [P, hPz] using P.last_edge_mem
    have heQ : s(some z, none) ∈ q.edges := by simpa [Q, hQz] using Q.last_edge_mem
    exact List.disjoint_left.mp hpq heP heQ
  rcases P.terminal_kind with hPOuter | hPShortcut
  · exact ⟨Q.edgeFinset, P.edgeFinset, hfinDisj.symm, hQη, hPη,
      local_of_projection Q hQE, off_of_projection P hPOuter hPE⟩
  · have hQOuter : Q.endpoint.1 ∈ cubicMetricSphere d x n := by
      rcases Q.terminal_kind with h | h
      · exact h
      · exact (hnotBothShortcut ⟨hPShortcut, h⟩).elim
    exact ⟨P.edgeFinset, Q.edgeFinset, hfinDisj, hPη, hQη,
      local_of_projection P hPE, off_of_projection Q hQOuter hQE⟩

theorem mem_disjointOccurrence_of_residual_terminal_overlap_avoidance
    {d n m : ℕ} {x y : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n) (hyD : y ∉ D)
    (z : {v : Cubic d // v ∈ cubicMetricBall d x n})
    (hzLocal : z.1 ∈ cubicMetricSphere d y m)
    (hOuterFar : ∀ v ∈ cubicMetricSphere d x n, m ≤ cubicL1Dist y v)
    (full shortcut : (radiusTerminalGraph
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) z True).Walk
        (some ⟨y, hyBall⟩) none)
    (havoid : ∀ e, e ∈ full.edges → e ∈ shortcut.edges →
      ∃ r : (radiusTerminalGraph
        (openOnFiniteEdges
          (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) z True).Walk
          (some ⟨y, hyBall⟩) none,
        e ∉ r.edges) :
    η ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D y m)
      (radiusConnectionEventOffExploration d x n D y
        (cubicMetricSphere d x n)) := by
  have hreach := TwoEdgeMenger.isEdgeReachable_two_of_walks_and_overlap_avoidance
    full shortcut havoid
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    TwoEdgeMenger.exists_two_edgeDisjoint_paths_of_isEdgeReachable_two hreach
  exact mem_disjointOccurrence_of_residual_terminal_paths hyBall hyD z hzLocal
    hOuterFar hp hq hpq

theorem residualTerminal_shortcut_edge_not_mem_full
    {d n : ℕ} {x y v : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n)
    (z : {w : Cubic d // w ∈ cubicMetricBall d x n})
    (hvOuter : v ∈ cubicMetricSphere d x n)
    (hzv : z.1 ≠ v)
    (q : (cubicGraph d).Walk y v)
    (hqopen : walkIsOpen
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) q)
    (hqball : ∀ w ∈ q.support, w ∈ cubicMetricBall d x n) :
    s((some z : RadiusTerminalVertex d x n), none) ∉
      (radiusTerminalFullWalkFrom ⟨y, hyBall⟩ z hvOuter q hqopen hqball).edges := by
  intro he
  unfold radiusTerminalFullWalkFrom at he
  change s((some z : RadiusTerminalVertex d x n), none) ∈
    (((radiusOpenBallWalkLiftOf hyBall
      (cubicMetricSphere_subset_ball d x n hvOuter) q hqopen hqball).walk.map
        (radiusOpenBallToTerminalHom
          (openOnFiniteEdges
            (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) z True)).concat
      (radiusTerminalGraph_adj_sink_iff.mpr (Or.inl hvOuter))).edges at he
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
  simp only [List.mem_singleton] at he
  rcases he with he | he
  · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨f, _hf, hfe⟩ := he
    have hsink : none ∈ s((some z : RadiusTerminalVertex d x n), none) := by simp
    rw [← hfe] at hsink
    simp [radiusOpenBallToTerminalHom] at hsink
  · have hzvEq : z.1 = v := by
      change s((some z : RadiusTerminalVertex d x n), none) =
        s(some ⟨v, cubicMetricSphere_subset_ball d x n hvOuter⟩, none) at he
      rcases Sym2.eq_iff.mp he with h | h
      · exact congrArg Subtype.val (Option.some.inj h.1)
      · exact (Option.some_ne_none z h.1).elim
    exact hzv hzvEq

theorem exists_residual_prefixBallEdge_of_mem_full_and_shortcut
    {d n : ℕ} {x y v : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n)
    (z : {w : Cubic d // w ∈ cubicMetricBall d x n})
    (hvOuter : v ∈ cubicMetricSphere d x n)
    (hzv : z.1 ≠ v)
    (q : (cubicGraph d).Walk y v)
    (hqopen : walkIsOpen
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) q)
    (hqball : ∀ w ∈ q.support, w ∈ cubicMetricBall d x n)
    (t : (cubicGraph d).Walk y z.1)
    (htopen : walkIsOpen
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) t)
    (htball : ∀ w ∈ t.support, w ∈ cubicMetricBall d x n)
    (e : Sym2 (RadiusTerminalVertex d x n))
    (heFull : e ∈
      (radiusTerminalFullWalkFrom ⟨y, hyBall⟩ z hvOuter q hqopen hqball).edges)
    (heShortcut : e ∈
      (radiusTerminalShortcutWalkFrom ⟨y, hyBall⟩ z t htopen htball).edges) :
    ∃ f ∈ (radiusOpenBallWalkLiftOf hyBall z.2 t htopen htball).walk.edges,
      e = Sym2.map some f := by
  unfold radiusTerminalShortcutWalkFrom at heShortcut
  change e ∈
    (((radiusOpenBallWalkLiftOf hyBall z.2 t htopen htball).walk.map
      (radiusOpenBallToTerminalHom
        (openOnFiniteEdges
          (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) z True)).concat
      (radiusTerminalGraph_adj_sink_iff.mpr (Or.inr ⟨True.intro, rfl⟩))).edges
      at heShortcut
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at heShortcut
  simp only [List.mem_singleton] at heShortcut
  rcases heShortcut with he | he
  · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨f, hf, hfe⟩ := he
    exact ⟨f, hf, hfe.symm⟩
  · exfalso
    change e = s((some z : RadiusTerminalVertex d x n), none) at he
    apply residualTerminal_shortcut_edge_not_mem_full hyBall z hvOuter hzv
      q hqopen hqball
    rw [← he]
    exact heFull

theorem mapped_ballEdge_not_mem_radiusTerminalFullWalkFrom
    {d n : ℕ} {x y v : Cubic d} {D : Finset (Cubic d)}
    {η ζ : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n)
    (z : {w : Cubic d // w ∈ cubicMetricBall d x n})
    (hvOuter : v ∈ cubicMetricSphere d x n)
    (q : (cubicGraph d).Walk y v)
    (hqopenζ : walkIsOpen ζ q)
    (hζξ : ζ ⊆ openOnFiniteEdges
      (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η)
    (hqball : ∀ w ∈ q.support, w ∈ cubicMetricBall d x n)
    (f : Sym2 {w : Cubic d // w ∈ cubicMetricBall d x n})
    (ef : CubicEdge d) (hef : (ef : Sym2 (Cubic d)) = Sym2.map Subtype.val f)
    (heclosed : ef ∉ ζ) :
    Sym2.map some f ∉
      (radiusTerminalFullWalkFrom ⟨y, hyBall⟩ z hvOuter q
        (fun g hg ↦ hζξ (hqopenζ g hg)) hqball).edges := by
  intro he
  unfold radiusTerminalFullWalkFrom at he
  change Sym2.map some f ∈
    (((radiusOpenBallWalkLiftOf hyBall
      (cubicMetricSphere_subset_ball d x n hvOuter) q
        (fun g hg ↦ hζξ (hqopenζ g hg)) hqball).walk.map
      (radiusOpenBallToTerminalHom
        (openOnFiniteEdges
          (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) z True)).concat
      (radiusTerminalGraph_adj_sink_iff.mpr (Or.inl hvOuter))).edges at he
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
  simp only [List.mem_singleton] at he
  rcases he with he | he
  · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨g, hg, hgf⟩ := he
    have hgf' : g = f := by
      change Sym2.map some g = Sym2.map some f at hgf
      exact Sym2.map.injective (Option.some_injective _) hgf
    subst g
    have hfq : Sym2.map Subtype.val f ∈ q.edges := by
      rw [← (radiusOpenBallWalkLiftOf hyBall
        (cubicMetricSphere_subset_ball d x n hvOuter) q
          (fun g hg ↦ hζξ (hqopenζ g hg)) hqball).map_edges]
      exact List.mem_map.mpr ⟨f, hg, rfl⟩
    have hefopen := hqopenζ _ hfq
    apply heclosed
    have hsub : (⟨Sym2.map Subtype.val f, q.edges_subset_edgeSet hfq⟩ : CubicEdge d) = ef :=
      Subtype.ext hef.symm
    simpa [hsub] using hefopen
  · have hsink : none ∈ Sym2.map some f := by
      rw [he]
      simp
    simp at hsink

/-- Residual analogue of the first-sausage Menger lemma: if every edge in a
local prefix is non-pivotal for the off-exploration outer event, the local and
outer events have disjoint open witnesses. -/
theorem mem_disjointOccurrence_of_residual_nonpivotal_prefix_of_strict
    {d n m : ℕ} {x y : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n) (hyD : y ∉ D)
    (z : {v : Cubic d // v ∈ cubicMetricBall d x n})
    (hzLocal : z.1 ∈ cubicMetricSphere d y m)
    (hOuterFar : ∀ v ∈ cubicMetricSphere d x n, m < cubicL1Dist y v)
    (hη : η ∈ radiusConnectionEventOffExploration d x n D y
      (cubicMetricSphere d x n))
    (t : (cubicGraph d).Walk y z.1)
    (htopen : walkIsOpen
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) t)
    (htball : ∀ v ∈ t.support, v ∈ cubicMetricBall d x n)
    (hnonpiv : ∀ e ∈ walkEdgeFinset t,
      ¬IsPivotal (radiusConnectionEventOffExploration d x n D y
        (cubicMetricSphere d x n)) e η) :
    η ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D y m)
      (radiusConnectionEventOffExploration d x n D y
        (cubicMetricSphere d x n)) := by
  classical
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let ξ := openOnFiniteEdges E η
  rcases hη with ⟨v, hvOuter, q, hqopen, hqsub, hqoff⟩
  have hqopenξ : walkIsOpen ξ q := by
    intro g hg
    let e : CubicEdge d := ⟨g, q.edges_subset_edgeSet hg⟩
    exact ⟨hqsub ((mem_walkEdgeFinset_iff q e).mpr hg), hqopen g hg⟩
  have hqball : ∀ w ∈ q.support, w ∈ cubicMetricBall d x n := by
    apply walk_support_subset_cubicMetricBall_of_edges hyBall q
    intro e he
    exact Finset.mem_sdiff.mp (hqsub he) |>.1
  let full := radiusTerminalFullWalkFrom ⟨y, hyBall⟩ z hvOuter q hqopenξ hqball
  let shortcut := radiusTerminalShortcutWalkFrom ⟨y, hyBall⟩ z t htopen htball
  apply mem_disjointOccurrence_of_residual_terminal_overlap_avoidance hyBall hyD z
    hzLocal (fun v hv ↦ (hOuterFar v hv).le) full shortcut
  intro edge heFull heShortcut
  obtain ⟨f, hf, hedge⟩ :=
    exists_residual_prefixBallEdge_of_mem_full_and_shortcut hyBall z
      hvOuter (by
        intro hzv
        have hzdist := mem_cubicMetricSphere_iff_l1Dist_eq.mp hzLocal
        have hstrict := hOuterFar v hvOuter
        rw [← hzv, hzdist] at hstrict
        exact (Nat.lt_irrefl _ hstrict))
      q hqopenξ hqball t htopen htball edge
      heFull heShortcut
  have hft : Sym2.map Subtype.val f ∈ t.edges := by
    rw [← (radiusOpenBallWalkLiftOf hyBall z.2 t htopen htball).map_edges]
    exact List.mem_map.mpr ⟨f, hf, rfl⟩
  let ef : CubicEdge d := ⟨Sym2.map Subtype.val f, t.edges_subset_edgeSet hft⟩
  have hefT : ef ∈ walkEdgeFinset t := by
    rw [mem_walkEdgeFinset_iff]
    exact hft
  have hclosed : η \ {ef} ∈ radiusConnectionEventOffExploration d x n D y
      (cubicMetricSphere d x n) :=
    mem_diff_singleton_of_mem_increasingEvent_of_not_pivotal
      (isIncreasingEvent_connectionEventOff d E D y (cubicMetricSphere d x n))
      ⟨v, hvOuter, q, hqopen, hqsub, hqoff⟩ (hnonpiv ef hefT)
  rcases hclosed with ⟨v', hvOuter', q', hqopen', hqsub', hqoff'⟩
  let ζ := openOnFiniteEdges E (η \ {ef})
  have hqopenζ : walkIsOpen ζ q' := by
    intro g hg
    let e : CubicEdge d := ⟨g, q'.edges_subset_edgeSet hg⟩
    exact ⟨hqsub' ((mem_walkEdgeFinset_iff q' e).mpr hg), hqopen' g hg⟩
  have hζξ : ζ ⊆ ξ := by
    intro e he
    exact ⟨he.1, he.2.1⟩
  have hqball' : ∀ w ∈ q'.support, w ∈ cubicMetricBall d x n := by
    apply walk_support_subset_cubicMetricBall_of_edges hyBall q'
    intro e he
    exact Finset.mem_sdiff.mp (hqsub' he) |>.1
  refine ⟨radiusTerminalFullWalkFrom ⟨y, hyBall⟩ z hvOuter' q'
    (fun g hg ↦ hζξ (hqopenζ g hg)) hqball', ?_⟩
  rw [hedge]
  apply mapped_ballEdge_not_mem_radiusTerminalFullWalkFrom hyBall z hvOuter' q'
    hqopenζ hζξ hqball' f ef rfl
  intro hefζ
  exact hefζ.2.2 rfl

/-- Witness-specific residual Menger lemma.  Unlike the strict-distance
variant, this form only asks that the chosen local endpoint differ from the
endpoint of the supplied outer witness.  This is the form needed in the
borderline case where the local radius just reaches the outer sphere. -/
theorem mem_disjointOccurrence_of_residual_nonpivotal_prefix_of_witness
    {d n m : ℕ} {x y : Cubic d} {D : Finset (Cubic d)}
    {η : EdgeConfiguration d}
    (hyBall : y ∈ cubicMetricBall d x n) (hyD : y ∉ D)
    (z : {w : Cubic d // w ∈ cubicMetricBall d x n})
    (hzLocal : z.1 ∈ cubicMetricSphere d y m)
    (hOuterFar : ∀ w ∈ cubicMetricSphere d x n, m ≤ cubicL1Dist y w)
    {v : Cubic d} (hvOuter : v ∈ cubicMetricSphere d x n)
    (q : (cubicGraph d).Walk y v) (hqopen : walkIsOpen η q)
    (hqsub : walkEdgeFinset q ⊆
      cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D)
    (hqoff : ∀ w ∈ q.support.tail, w ∉ D)
    (hzv : z.1 ≠ v)
    (t : (cubicGraph d).Walk y z.1)
    (htopen : walkIsOpen
      (openOnFiniteEdges
        (cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D) η) t)
    (htball : ∀ w ∈ t.support, w ∈ cubicMetricBall d x n)
    (hnonpiv : ∀ e ∈ walkEdgeFinset t,
      ¬IsPivotal (radiusConnectionEventOffExploration d x n D y
        (cubicMetricSphere d x n)) e η) :
    η ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D y m)
      (radiusConnectionEventOffExploration d x n D y
        (cubicMetricSphere d x n)) := by
  classical
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let ξ := openOnFiniteEdges E η
  have hqopenξ : walkIsOpen ξ q := by
    intro g hg
    let e : CubicEdge d := ⟨g, q.edges_subset_edgeSet hg⟩
    exact ⟨hqsub ((mem_walkEdgeFinset_iff q e).mpr hg), hqopen g hg⟩
  have hqball : ∀ w ∈ q.support, w ∈ cubicMetricBall d x n := by
    apply walk_support_subset_cubicMetricBall_of_edges hyBall q
    intro e he
    exact Finset.mem_sdiff.mp (hqsub he) |>.1
  let full := radiusTerminalFullWalkFrom ⟨y, hyBall⟩ z hvOuter q hqopenξ hqball
  let shortcut := radiusTerminalShortcutWalkFrom ⟨y, hyBall⟩ z t htopen htball
  apply mem_disjointOccurrence_of_residual_terminal_overlap_avoidance hyBall hyD z
    hzLocal hOuterFar full shortcut
  intro edge heFull heShortcut
  obtain ⟨f, hf, hedge⟩ :=
    exists_residual_prefixBallEdge_of_mem_full_and_shortcut hyBall z
      hvOuter hzv q hqopenξ hqball t htopen htball edge heFull heShortcut
  have hft : Sym2.map Subtype.val f ∈ t.edges := by
    rw [← (radiusOpenBallWalkLiftOf hyBall z.2 t htopen htball).map_edges]
    exact List.mem_map.mpr ⟨f, hf, rfl⟩
  let ef : CubicEdge d := ⟨Sym2.map Subtype.val f, t.edges_subset_edgeSet hft⟩
  have hefT : ef ∈ walkEdgeFinset t := by
    rw [mem_walkEdgeFinset_iff]
    exact hft
  have hclosed : η \ {ef} ∈ radiusConnectionEventOffExploration d x n D y
      (cubicMetricSphere d x n) :=
    mem_diff_singleton_of_mem_increasingEvent_of_not_pivotal
      (isIncreasingEvent_connectionEventOff d E D y (cubicMetricSphere d x n))
      ⟨v, hvOuter, q, hqopen, hqsub, hqoff⟩ (hnonpiv ef hefT)
  rcases hclosed with ⟨v', hvOuter', q', hqopen', hqsub', hqoff'⟩
  let ζ := openOnFiniteEdges E (η \ {ef})
  have hqopenζ : walkIsOpen ζ q' := by
    intro g hg
    let e : CubicEdge d := ⟨g, q'.edges_subset_edgeSet hg⟩
    exact ⟨hqsub' ((mem_walkEdgeFinset_iff q' e).mpr hg), hqopen' g hg⟩
  have hζξ : ζ ⊆ ξ := by
    intro e he
    exact ⟨he.1, he.2.1⟩
  have hqball' : ∀ w ∈ q'.support, w ∈ cubicMetricBall d x n := by
    apply walk_support_subset_cubicMetricBall_of_edges hyBall q'
    intro e he
    exact Finset.mem_sdiff.mp (hqsub' he) |>.1
  refine ⟨radiusTerminalFullWalkFrom ⟨y, hyBall⟩ z hvOuter' q'
    (fun g hg ↦ hζξ (hqopenζ g hg)) hqball', ?_⟩
  rw [hedge]
  apply mapped_ballEdge_not_mem_radiusTerminalFullWalkFrom hyBall z hvOuter' q'
    hqopenζ hζξ hqball' f ef rfl
  intro hefζ
  exact hefζ.2.2 rfl

theorem firstHitTail_edge_not_pivotal_off_of_lt_nextSausageGap
    {d n r : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hprefix.1)
    (hmark : (radiusPivotalDarts hprefix.1).idxOf a + 1 = rs.length)
    (hm : r + 1 ≤ cubicL1Dist a.toProd.2 (canonicalRadiusWitness hprefix.1).endpoint)
    (hlong : r < sausageGap d x n ω (rs.length + 1)) :
    let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
    let q := pivotalTailWalk hprefix.1 ha
    let K := walkFirstRadiusHitIndex q hm
    ∀ ef ∈ walkEdgeFinset (q.take K),
      ¬IsPivotal (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) ef ω := by
  classical
  dsimp only
  let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let q := pivotalTailWalk hprefix.1 ha
  let K := walkFirstRadiusHitIndex q hm
  intro ef hef hpivR
  have hqE : walkEdgeFinset q ⊆ E := by
    simpa [q, E, D] using pivotalTailWalk_edgeFinset_subset_exterior hprefix.1 ha
  have hefE : ef ∈ E := by
    apply hqE
    rw [mem_walkEdgeFinset_iff] at hef ⊢
    exact (SimpleGraph.Walk.isSubwalk_take q K).edges_subset hef
  have hefNotF : ef ∉ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω := by
    intro hefF
    have hefInc : ef ∈ radiusIncidentEdgesOf d x n D := by
      simpa [D, radiusDeletedIncidentEdges] using hefF
    exact (Finset.mem_sdiff.mp hefE).2 hefInc
  have hpivA : IsPivotal (radiusConnectionEvent d x n) ef ω :=
    (isPivotal_radiusConnectionEvent_iff_offExploration hprefix.1 ha hefNotF).mpr hpivR
  have hefEdges : (ef : Sym2 (Cubic d)) ∈ (q.take K).edges :=
    (mem_walkEdgeFinset_iff (q.take K) ef).mp hef
  rw [SimpleGraph.Walk.edges] at hefEdges
  rcases List.mem_map.mp hefEdges with ⟨b, hbHit, hbe⟩
  have hbEdge : cubicEdgeOfDart b = ef := Subtype.ext hbe
  have hbPiv : IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart b) ω := by
    rw [hbEdge]
    exact hpivA
  have hbW : b ∈ (canonicalRadiusWitness hprefix.1).walk.darts := by
    have hbq : b ∈ q.darts := (SimpleGraph.Walk.isSubwalk_take q K).darts_subset hbHit
    change b ∈ (pivotalTailWalk hprefix.1 ha).darts at hbq
    rw [pivotalTailWalk_darts] at hbq
    exact List.mem_of_mem_drop hbq
  have hb : b ∈ radiusPivotalDarts hprefix.1 :=
    (mem_radiusPivotalDarts_iff hprefix.1 b).mpr ⟨hbW, hbPiv⟩
  have hshort := nextSausageGap_lt_of_pivotalDart_mem_tail_firstHit
    hprefix.1 ha hb hm (by simpa [q, K] using hbHit)
  have harg : (radiusPivotalDarts hprefix.1).idxOf a + 2 = rs.length + 1 := by
    omega
  rw [harg] at hshort
  omega

/-- Strict-budget form of Grimmett's deterministic residual inclusion in
(5.16): a long next sausage yields disjoint local and outer witnesses off the
marked exploration. -/
theorem sausageGapPrefixNextLong_mem_residual_disjointOccurrence_of_strict
    {d n r : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hprefix.1)
    (hmark : (radiusPivotalDarts hprefix.1).idxOf a + 1 = rs.length)
    (hbudget : rs.sum + r + (rs.length + 1) < n)
    (hlong : r < sausageGap d x n ω (rs.length + 1)) :
    let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
    ω ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D a.toProd.2 (r + 1))
      (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) := by
  classical
  dsimp only
  let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let q := pivotalTailWalk hprefix.1 ha
  have hm : r + 1 ≤ cubicL1Dist a.toProd.2 (canonicalRadiusWitness hprefix.1).endpoint :=
    markedPivotalDart_outerSphere_dist_ge hprefix ha hmark (by omega)
      (canonicalRadiusWitness hprefix.1).sphere_mem
  let K := walkFirstRadiusHitIndex q hm
  let t := q.take K
  let y := q.getVert K
  have heBall : cubicEdgeOfDart a ∈ cubicMetricBallEdges d x n :=
    (mem_radiusDeletedBoundaryEdges_iff.mp
      (cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hprefix.1 ha)).1
  have hyBall : a.toProd.2 ∈ cubicMetricBall d x n := by
    apply endpoint_mem_cubicMetricBall_of_edge_mem heBall
    change a.toProd.2 ∈ s(a.toProd.1, a.toProd.2)
    simp
  have haD : a.toProd.2 ∉ D := by
    simpa [D] using pivotalDart_snd_not_mem_radiusDeletedReachableVertices hprefix.1 ha
  have hqE : walkEdgeFinset q ⊆ E := by
    simpa [q, E, D] using pivotalTailWalk_edgeFinset_subset_exterior hprefix.1 ha
  have hqopen : walkIsOpen (openOnFiniteEdges E ω) q := by
    simpa [q, E, D] using pivotalTailWalk_isOpen_openOnExterior hprefix.1 ha
  have hqball : ∀ z ∈ q.support, z ∈ cubicMetricBall d x n :=
    walk_support_subset_cubicMetricBall_of_edges hyBall q
      (hqE.trans Finset.sdiff_subset)
  have htopen : walkIsOpen (openOnFiniteEdges E ω) t :=
    walkIsOpen_take q hqopen K
  have htball : ∀ z ∈ t.support, z ∈ cubicMetricBall d x n := by
    intro z hz
    exact hqball z ((SimpleGraph.Walk.isSubwalk_take q K).support_subset hz)
  have hyLocal : y ∈ cubicMetricSphere d a.toProd.2 (r + 1) := by
    rw [mem_cubicMetricSphere_iff_l1Dist_eq]
    simpa [y, q, K] using walkFirstRadiusHit_dist_eq q hm
  let z : {v : Cubic d // v ∈ cubicMetricBall d x n} :=
    ⟨y, htball y (by simp [t, y])⟩
  have hR : ω ∈ radiusConnectionEventOffExploration d x n D a.toProd.2
      (cubicMetricSphere d x n) := by
    apply (radiusConnectionEvent_iff_connectionEventOffExploration_of_agree
      hprefix.1 ha ?_).mp hprefix.1
    intro f hf
    rfl
  have hnonpiv : ∀ ef ∈ walkEdgeFinset t,
      ¬IsPivotal (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) ef ω := by
    intro ef hef hpivR
    have hefE : ef ∈ E := by
      apply hqE
      rw [mem_walkEdgeFinset_iff] at hef ⊢
      exact (SimpleGraph.Walk.isSubwalk_take q K).edges_subset hef
    have hefNotF : ef ∉ radiusDeletedIncidentEdges d x n (cubicEdgeOfDart a) ω := by
      intro hefF
      have hefInc : ef ∈ radiusIncidentEdgesOf d x n D := by
        simpa [D, radiusDeletedIncidentEdges] using hefF
      exact (Finset.mem_sdiff.mp hefE).2 hefInc
    have hpivA : IsPivotal (radiusConnectionEvent d x n) ef ω :=
      (isPivotal_radiusConnectionEvent_iff_offExploration hprefix.1 ha hefNotF).mpr hpivR
    have hefEdges : (ef : Sym2 (Cubic d)) ∈ t.edges :=
      (mem_walkEdgeFinset_iff t ef).mp hef
    rw [SimpleGraph.Walk.edges] at hefEdges
    rcases List.mem_map.mp hefEdges with ⟨b, hbHit, hbe⟩
    have hbEdge : cubicEdgeOfDart b = ef := Subtype.ext hbe
    have hbPiv : IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart b) ω := by
      rw [hbEdge]
      exact hpivA
    have hbW : b ∈ (canonicalRadiusWitness hprefix.1).walk.darts := by
      have hbq : b ∈ q.darts :=
        (SimpleGraph.Walk.isSubwalk_take q K).darts_subset hbHit
      change b ∈ (pivotalTailWalk hprefix.1 ha).darts at hbq
      rw [pivotalTailWalk_darts] at hbq
      exact List.mem_of_mem_drop hbq
    have hb : b ∈ radiusPivotalDarts hprefix.1 :=
      (mem_radiusPivotalDarts_iff hprefix.1 b).mpr ⟨hbW, hbPiv⟩
    have hshort := nextSausageGap_lt_of_pivotalDart_mem_tail_firstHit
      hprefix.1 ha hb hm (by simpa [t, q, K] using hbHit)
    have harg : (radiusPivotalDarts hprefix.1).idxOf a + 2 = rs.length + 1 := by
      omega
    rw [harg] at hshort
    omega
  apply mem_disjointOccurrence_of_residual_nonpivotal_prefix_of_strict
    hyBall haD z (by simpa [z] using hyLocal)
  · intro v hv
    exact markedPivotalDart_outerSphere_dist_gt hprefix ha hmark hbudget hv
  · exact hR
  · simpa [t, q, K, E, D] using htopen
  · intro v hv
    exact htball v (by simpa [t, q, K, z] using hv)
  · intro ef hef
    apply hnonpiv ef
    simpa [t, q, K, z] using hef

/-- Endpoint branch of the residual inclusion.  If the first local hit is the
outer endpoint itself, the doubled-target Menger theorem supplies two
edge-disjoint outer connections. -/
theorem sausageGapPrefixNextLong_mem_residual_disjointOccurrence_endpoint
    {d n r : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hprefix.1)
    (hmark : (radiusPivotalDarts hprefix.1).idxOf a + 1 = rs.length)
    (hbudget : rs.sum + r + (rs.length + 1) ≤ n)
    (hlong : r < sausageGap d x n ω (rs.length + 1))
    (hend : (pivotalTailWalk hprefix.1 ha).getVert
      (walkFirstRadiusHitIndex (pivotalTailWalk hprefix.1 ha)
        (markedPivotalDart_outerSphere_dist_ge hprefix ha hmark hbudget
          (canonicalRadiusWitness hprefix.1).sphere_mem)) =
        (canonicalRadiusWitness hprefix.1).endpoint) :
    let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
    ω ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D a.toProd.2 (r + 1))
      (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) := by
  classical
  dsimp only
  let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let ξ := openOnFiniteEdges E ω
  let q := pivotalTailWalk hprefix.1 ha
  have hm : r + 1 ≤ cubicL1Dist a.toProd.2 (canonicalRadiusWitness hprefix.1).endpoint :=
    markedPivotalDart_outerSphere_dist_ge hprefix ha hmark hbudget
      (canonicalRadiusWitness hprefix.1).sphere_mem
  let K := walkFirstRadiusHitIndex q hm
  have hKlen : K = q.length := by
    apply walkFirstRadiusHitIndex_eq_length_of_getVert_eq_end q
      (pivotalTailWalk_isPath hprefix.1 ha) hm
    simpa [q, K] using hend
  have heBall : cubicEdgeOfDart a ∈ cubicMetricBallEdges d x n :=
    (mem_radiusDeletedBoundaryEdges_iff.mp
      (cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hprefix.1 ha)).1
  have hyBall : a.toProd.2 ∈ cubicMetricBall d x n := by
    apply endpoint_mem_cubicMetricBall_of_edge_mem heBall
    change a.toProd.2 ∈ s(a.toProd.1, a.toProd.2)
    simp
  have hyD : a.toProd.2 ∉ D := by
    simpa [D] using pivotalDart_snd_not_mem_radiusDeletedReachableVertices hprefix.1 ha
  have hqE : walkEdgeFinset q ⊆ E := by
    simpa [q, E, D] using pivotalTailWalk_edgeFinset_subset_exterior hprefix.1 ha
  have hqopen : walkIsOpen ξ q := by
    simpa [q, ξ, E, D] using pivotalTailWalk_isOpen_openOnExterior hprefix.1 ha
  have hqball : ∀ z ∈ q.support, z ∈ cubicMetricBall d x n :=
    walk_support_subset_cubicMetricBall_of_edges hyBall q
      (hqE.trans Finset.sdiff_subset)
  have hR : ω ∈ radiusConnectionEventOffExploration d x n D a.toProd.2
      (cubicMetricSphere d x n) := by
    refine ⟨(canonicalRadiusWitness hprefix.1).endpoint,
      (canonicalRadiusWitness hprefix.1).sphere_mem, q, ?_, hqE, ?_⟩
    · exact fun g hg ↦ (hqopen g hg).2
    · intro z hz
      exact pivotalTailWalk_support_outside_deletedReachable hprefix.1 ha z
        (List.mem_of_mem_tail hz)
  have hnonpivQ : ∀ ef ∈ walkEdgeFinset q,
      ¬IsPivotal (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) ef ω := by
    intro ef hef
    apply firstHitTail_edge_not_pivotal_off_of_lt_nextSausageGap
      hprefix ha hmark hm hlong ef
    have hef' := (mem_walkEdgeFinset_iff q ef).mp hef
    change ef ∈ walkEdgeFinset (q.take K)
    have htake : q.edges.take q.length = q.edges :=
      (List.take_eq_self_iff q.edges).mpr (Nat.le_of_eq q.length_edges)
    rw [mem_walkEdgeFinset_iff, SimpleGraph.Walk.edges_take, hKlen, htake]
    exact hef'
  let T := cubicMetricSphereInBall d x n
  let endpoint : {z : Cubic d // z ∈ cubicMetricBall d x n} :=
    ⟨(canonicalRadiusWitness hprefix.1).endpoint,
      cubicMetricSphere_subset_ball d x n (canonicalRadiusWitness hprefix.1).sphere_mem⟩
  have hendT : endpoint ∈ T := by
    simpa [endpoint, T] using (canonicalRadiusWitness hprefix.1).sphere_mem
  let p₀ := (radiusOpenBallWalkLiftOf hyBall endpoint.2 q hqopen hqball).walk
  have havoid : ∀ f : Sym2 {z : Cubic d // z ∈ cubicMetricBall d x n},
      ∃ t ∈ T, ∃ p : (radiusOpenBallGraph ξ).Walk ⟨a.toProd.2, hyBall⟩ t,
        f ∉ p.edges := by
    intro f
    by_cases hfedge : f ∈ (radiusOpenBallGraph ξ).edgeSet
    · let ef : CubicEdge d := ⟨Sym2.map Subtype.val f, by
          induction f using Sym2.inductionOn with
          | _ u v =>
              have huv : (radiusOpenBallGraph ξ).Adj u v := by
                rw [← SimpleGraph.mem_edgeSet]
                exact hfedge
              obtain ⟨g, hg, _⟩ := huv
              change s(u.1, v.1) ∈ (cubicGraph d).edgeSet
              exact hg ▸ g.2⟩
      by_cases hefq : (ef : Sym2 (Cubic d)) ∈ q.edges
      · have hefFin : ef ∈ walkEdgeFinset q := (mem_walkEdgeFinset_iff q ef).mpr hefq
        have hclosed : ω \ {ef} ∈ radiusConnectionEventOffExploration d x n D
            a.toProd.2 (cubicMetricSphere d x n) :=
          mem_diff_singleton_of_mem_increasingEvent_of_not_pivotal
            (isIncreasingEvent_connectionEventOff d E D a.toProd.2
              (cubicMetricSphere d x n)) hR (hnonpivQ ef hefFin)
        rcases hclosed with ⟨v, hv, q', hq'open, hq'sub, hq'off⟩
        have hq'openξ : walkIsOpen ξ q' := by
          intro g hg
          let e : CubicEdge d := ⟨g, q'.edges_subset_edgeSet hg⟩
          exact ⟨hq'sub ((mem_walkEdgeFinset_iff q' e).mpr hg), (hq'open g hg).1⟩
        have hq'ball : ∀ z ∈ q'.support, z ∈ cubicMetricBall d x n :=
          walk_support_subset_cubicMetricBall_of_edges hyBall q'
            (hq'sub.trans Finset.sdiff_subset)
        let t' : {z : Cubic d // z ∈ cubicMetricBall d x n} :=
          ⟨v, cubicMetricSphere_subset_ball d x n hv⟩
        let P := radiusOpenBallWalkLiftOf hyBall t'.2 q' hq'openξ hq'ball
        refine ⟨t', by simpa [t', T] using hv, P.walk, ?_⟩
        intro hfP
        have hfq' : Sym2.map Subtype.val f ∈ q'.edges := by
          rw [← P.map_edges]
          exact List.mem_map.mpr ⟨f, hfP, rfl⟩
        have hopen := hq'open _ hfq'
        have heq :
            (⟨Sym2.map Subtype.val f, q'.edges_subset_edgeSet hfq'⟩ : CubicEdge d) = ef := by
          apply Subtype.ext
          rfl
        rw [heq] at hopen
        exact hopen.2 rfl
      · refine ⟨endpoint, hendT, p₀, ?_⟩
        intro hfp
        apply hefq
        change f ∈ (radiusOpenBallWalkLiftOf hyBall endpoint.2 q hqopen hqball).walk.edges at hfp
        have hmap : Sym2.map Subtype.val f ∈
            (radiusOpenBallWalkLiftOf hyBall endpoint.2 q hqopen hqball).walk.edges.map
              (Sym2.map Subtype.val) :=
          List.mem_map.mpr ⟨f, hfp, rfl⟩
        rw [(radiusOpenBallWalkLiftOf hyBall endpoint.2 q hqopen hqball).map_edges] at hmap
        simpa [ef] using hmap
    · refine ⟨endpoint, hendT, p₀, ?_⟩
      intro hfp
      exact hfedge (p₀.edges_subset_edgeSet hfp)
  obtain ⟨u, v, p, s, hps⟩ :=
    TwoEdgeMenger.exists_two_edgeDisjoint_walks_to_finset
      (G := radiusOpenBallGraph ξ) hendT p₀ havoid
  exact mem_disjointOccurrence_of_edgeDisjoint_residual_outerWalks
    (D := D) (η := ω) (m := r + 1) (u := u.1) (v := v.1) hyBall hyD
    ((mem_cubicMetricSphereInBall u.1).mp u.2)
    ((mem_cubicMetricSphereInBall v.1).mp v.2)
    (fun w hw ↦ markedPivotalDart_outerSphere_dist_ge hprefix ha hmark hbudget hw)
    p s hps

/-- Non-endpoint branch of the exact-budget residual inclusion.  The
canonical pivotal tail itself supplies the outer witness, while the local
first-hit prefix supplies the short-radius witness. -/
theorem sausageGapPrefixNextLong_mem_residual_disjointOccurrence_nonendpoint
    {d n r : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hprefix.1)
    (hmark : (radiusPivotalDarts hprefix.1).idxOf a + 1 = rs.length)
    (hbudget : rs.sum + r + (rs.length + 1) ≤ n)
    (hlong : r < sausageGap d x n ω (rs.length + 1))
    (hend : (pivotalTailWalk hprefix.1 ha).getVert
      (walkFirstRadiusHitIndex (pivotalTailWalk hprefix.1 ha)
        (markedPivotalDart_outerSphere_dist_ge hprefix ha hmark hbudget
          (canonicalRadiusWitness hprefix.1).sphere_mem)) ≠
        (canonicalRadiusWitness hprefix.1).endpoint) :
    let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
    ω ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D a.toProd.2 (r + 1))
      (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) := by
  classical
  dsimp only
  let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
  let E := cubicMetricBallEdges d x n \ radiusIncidentEdgesOf d x n D
  let q := pivotalTailWalk hprefix.1 ha
  have hm : r + 1 ≤ cubicL1Dist a.toProd.2
      (canonicalRadiusWitness hprefix.1).endpoint :=
    markedPivotalDart_outerSphere_dist_ge hprefix ha hmark hbudget
      (canonicalRadiusWitness hprefix.1).sphere_mem
  let K := walkFirstRadiusHitIndex q hm
  let t := q.take K
  let y := q.getVert K
  have heBall : cubicEdgeOfDart a ∈ cubicMetricBallEdges d x n :=
    (mem_radiusDeletedBoundaryEdges_iff.mp
      (cubicEdgeOfDart_mem_radiusDeletedBoundaryEdges hprefix.1 ha)).1
  have hyBall : a.toProd.2 ∈ cubicMetricBall d x n := by
    apply endpoint_mem_cubicMetricBall_of_edge_mem heBall
    change a.toProd.2 ∈ s(a.toProd.1, a.toProd.2)
    simp
  have hyD : a.toProd.2 ∉ D := by
    simpa [D] using pivotalDart_snd_not_mem_radiusDeletedReachableVertices hprefix.1 ha
  have hqE : walkEdgeFinset q ⊆ E := by
    simpa [q, E, D] using pivotalTailWalk_edgeFinset_subset_exterior hprefix.1 ha
  have hqopenξ : walkIsOpen (openOnFiniteEdges E ω) q := by
    simpa [q, E, D] using pivotalTailWalk_isOpen_openOnExterior hprefix.1 ha
  have hqopen : walkIsOpen ω q := by
    intro g hg
    exact (hqopenξ g hg).2
  have hqball : ∀ z ∈ q.support, z ∈ cubicMetricBall d x n :=
    walk_support_subset_cubicMetricBall_of_edges hyBall q
      (hqE.trans Finset.sdiff_subset)
  have hqoff : ∀ z ∈ q.support.tail, z ∉ D := by
    intro z hz
    exact pivotalTailWalk_support_outside_deletedReachable hprefix.1 ha z
      (List.mem_of_mem_tail hz)
  have htopen : walkIsOpen (openOnFiniteEdges E ω) t :=
    walkIsOpen_take q hqopenξ K
  have htball : ∀ z ∈ t.support, z ∈ cubicMetricBall d x n := by
    intro z hz
    exact hqball z ((SimpleGraph.Walk.isSubwalk_take q K).support_subset hz)
  have hyLocal : y ∈ cubicMetricSphere d a.toProd.2 (r + 1) := by
    rw [mem_cubicMetricSphere_iff_l1Dist_eq]
    simpa [y, q, K] using walkFirstRadiusHit_dist_eq q hm
  let z : {v : Cubic d // v ∈ cubicMetricBall d x n} :=
    ⟨y, htball y (by simp [t, y])⟩
  have hnonpiv : ∀ ef ∈ walkEdgeFinset t,
      ¬IsPivotal (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) ef ω := by
    intro ef hef
    apply firstHitTail_edge_not_pivotal_off_of_lt_nextSausageGap
      hprefix ha hmark hm hlong ef
    simpa [t, q, K, D] using hef
  apply mem_disjointOccurrence_of_residual_nonpivotal_prefix_of_witness
    (v := (canonicalRadiusWitness hprefix.1).endpoint) (q := q) (t := t)
    hyBall hyD z (by simpa [z] using hyLocal)
  · intro w hw
    exact markedPivotalDart_outerSphere_dist_ge hprefix ha hmark hbudget hw
  · exact (canonicalRadiusWitness hprefix.1).sphere_mem
  · exact hqopen
  · simpa [E, D] using hqE
  · simpa [D] using hqoff
  · simpa [z, y, q, K] using hend
  · simpa [t, E, D] using htopen
  · exact htball
  · simpa [t, D] using hnonpiv

/-- Exact deterministic residual inclusion underlying Grimmett's equation
(5.16).  The non-strict budget includes the limiting case in which the first
local radius hit is already the endpoint on the outer sphere. -/
theorem sausageGapPrefixNextLong_mem_residual_disjointOccurrence
    {d n r : ℕ} {x : Cubic d} {ω : EdgeConfiguration d} {rs : List ℕ}
    (hprefix : ω ∈ sausageGapPrefixEvent d x n rs)
    {a : (cubicGraph d).Dart} (ha : a ∈ radiusPivotalDarts hprefix.1)
    (hmark : (radiusPivotalDarts hprefix.1).idxOf a + 1 = rs.length)
    (hbudget : rs.sum + r + (rs.length + 1) ≤ n)
    (hlong : r < sausageGap d x n ω (rs.length + 1)) :
    let D := radiusDeletedReachableVertices d x n (cubicEdgeOfDart a) ω
    ω ∈ OpenWitnessDisjointOccurrence
      (residualLocalRadiusEvent d x n D a.toProd.2 (r + 1))
      (radiusConnectionEventOffExploration d x n D a.toProd.2
        (cubicMetricSphere d x n)) := by
  dsimp only
  by_cases hend : (pivotalTailWalk hprefix.1 ha).getVert
      (walkFirstRadiusHitIndex (pivotalTailWalk hprefix.1 ha)
        (markedPivotalDart_outerSphere_dist_ge hprefix ha hmark hbudget
          (canonicalRadiusWitness hprefix.1).sphere_mem)) =
        (canonicalRadiusWitness hprefix.1).endpoint
  · exact sausageGapPrefixNextLong_mem_residual_disjointOccurrence_endpoint
      hprefix ha hmark hbudget hlong hend
  · exact sausageGapPrefixNextLong_mem_residual_disjointOccurrence_nonendpoint
      hprefix ha hmark hbudget hlong hend

end Percolation

#print axioms Percolation.mem_disjointOccurrence_of_residual_nonpivotal_prefix_of_witness
#print axioms Percolation.sausageGapPrefixNextLong_mem_residual_disjointOccurrence
