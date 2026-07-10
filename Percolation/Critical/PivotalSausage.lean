import Percolation.Critical.Radius
import Percolation.Core.TwoEdgeMenger
import Percolation.Core.TwoEdgeMengerToSet
import Percolation.Bernoulli.Russo

/-!
# Pivotal sausages for finite radius events

This file formalizes the ordered pivotal-edge and gap variables used in Grimmett §5.2,
especially Lemmas 5.12 and 5.17.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval BigOperators

/-- Regard a dart of the cubic graph as a cubic edge. -/
def cubicEdgeOfDart {d : ℕ} (a : (cubicGraph d).Dart) : CubicEdge d :=
  ⟨a.edge, by
    change s(a.fst, a.snd) ∈ (cubicGraph d).edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact a.adj⟩

/-- A path witness for `Aₙ(x)`, including its finite-support certificate. -/
structure RadiusConnectionWitness (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) where
  endpoint : Cubic d
  sphere_mem : endpoint ∈ cubicMetricSphere d x n
  walk : (cubicGraph d).Walk x endpoint
  isPath : walk.IsPath
  isOpen : walkIsOpen ω walk
  edge_subset : walkEdgeFinset walk ⊆ cubicMetricBallEdges d x n

theorem exists_radiusConnectionWitness {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n) :
    Nonempty (RadiusConnectionWitness d x n ω) := by
  rcases hω with ⟨y, hy, w, hopen, hsub⟩
  let q : (cubicGraph d).Walk x y := (w.toPath : (cubicGraph d).Walk x y)
  refine ⟨⟨y, hy, q, w.toPath.2, walkIsOpen_toPath w hopen, ?_⟩⟩
  intro e he
  rw [mem_walkEdgeFinset_iff] at he
  apply hsub
  rw [mem_walkEdgeFinset_iff]
  exact SimpleGraph.Walk.edges_toPath_subset w he

/-- A fixed witness, used only to turn the source's path-independent pivotal ordering into a
total Lean function. -/
noncomputable def canonicalRadiusWitness {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    RadiusConnectionWitness d x n ω :=
  Classical.choice (exists_radiusConnectionWitness hω)

theorem firstRadiusHit_exists {d n m : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) (hmn : m ≤ n) :
    ∃ k : ℕ, k ≤ (canonicalRadiusWitness hω).walk.length ∧
      m ≤ cubicL1Dist x ((canonicalRadiusWitness hω).walk.getVert k) := by
  exact ⟨(canonicalRadiusWitness hω).walk.length, le_rfl, by
    simpa [mem_cubicMetricSphere_iff_l1Dist_eq.mp
      (canonicalRadiusWitness hω).sphere_mem] using hmn⟩

noncomputable def firstRadiusHitIndex {d n m : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) (hmn : m ≤ n) : ℕ :=
  Nat.find (firstRadiusHit_exists hω hmn)

noncomputable def firstRadiusHitWalk {d n m : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) (hmn : m ≤ n) :
    (cubicGraph d).Walk x
      ((canonicalRadiusWitness hω).walk.getVert (firstRadiusHitIndex hω hmn)) :=
  (canonicalRadiusWitness hω).walk.take (firstRadiusHitIndex hω hmn)

theorem firstRadiusHitIndex_spec {d n m : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) (hmn : m ≤ n) :
    firstRadiusHitIndex hω hmn ≤ (canonicalRadiusWitness hω).walk.length ∧
      m ≤ cubicL1Dist x
        ((canonicalRadiusWitness hω).walk.getVert (firstRadiusHitIndex hω hmn)) := by
  exact Nat.find_spec (firstRadiusHit_exists hω hmn)

theorem firstRadiusHit_dist_eq {d n m : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) (hmn : m ≤ n) :
    cubicL1Dist x
      ((canonicalRadiusWitness hω).walk.getVert (firstRadiusHitIndex hω hmn)) = m := by
  let k := firstRadiusHitIndex hω hmn
  have hk := firstRadiusHitIndex_spec hω hmn
  change cubicL1Dist x ((canonicalRadiusWitness hω).walk.getVert k) = m
  change k ≤ (canonicalRadiusWitness hω).walk.length ∧
    m ≤ cubicL1Dist x ((canonicalRadiusWitness hω).walk.getVert k) at hk
  by_cases hkzero : k = 0
  · have hmzero : m = 0 := by simpa [k, hkzero] using hk.2
    simp [k, hkzero, hmzero]
  · let j := k - 1
    have hksucc : k = j + 1 := by omega
    have hjlt : cubicL1Dist x ((canonicalRadiusWitness hω).walk.getVert j) < m := by
      apply lt_of_not_ge
      intro hj
      exact Nat.find_min (firstRadiusHit_exists hω hmn)
        (show j < k by omega) ⟨by omega, hj⟩
    have hjlen : j < (canonicalRadiusWitness hω).walk.length := by omega
    have hadj := (canonicalRadiusWitness hω).walk.adj_getVert_succ hjlen
    rcases (cubicGraph_adj_iff_exists_stepFrom _ _).mp hadj with ⟨a, ha⟩
    have hupper : cubicL1Dist x
        ((canonicalRadiusWitness hω).walk.getVert (j + 1)) ≤ m := by
      calc
        cubicL1Dist x ((canonicalRadiusWitness hω).walk.getVert (j + 1)) ≤
            cubicL1Dist x ((canonicalRadiusWitness hω).walk.getVert j) +
              cubicL1Dist ((canonicalRadiusWitness hω).walk.getVert j)
                ((canonicalRadiusWitness hω).walk.getVert (j + 1)) :=
          cubicL1Dist_triangle _ _ _
        _ = cubicL1Dist x ((canonicalRadiusWitness hω).walk.getVert j) + 1 := by
          rw [ha, cubicL1Dist_stepFrom]
        _ ≤ m := by omega
    rw [hksucc]
    exact le_antisymm hupper (by simpa [hksucc] using hk.2)

theorem firstRadiusHitWalk_dart_fst_dist_lt {d n m : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) (hmn : m ≤ n)
    {a : (cubicGraph d).Dart} (ha : a ∈ (firstRadiusHitWalk hω hmn).darts) :
    cubicL1Dist x a.fst < m := by
  let k := firstRadiusHitIndex hω hmn
  have hk := firstRadiusHitIndex_spec hω hmn
  rw [firstRadiusHitWalk, SimpleGraph.Walk.darts_take] at ha
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  have hilength : i < k := by
    simpa [List.length_take, Nat.min_eq_left hk.1] using hi
  have hiW : i < (canonicalRadiusWitness hω).walk.darts.length := by
    simpa using lt_of_lt_of_le hilength hk.1
  have haeq := (canonicalRadiusWitness hω).walk.darts_getElem_eq_getVert i hiW
  have hiaW : (canonicalRadiusWitness hω).walk.darts[i] = a := by
    rw [← hia]
    simp
  have hafst : a.fst = (canonicalRadiusWitness hω).walk.getVert i := by
    rw [← hiaW, haeq]
  rw [hafst]
  apply lt_of_not_ge
  intro hge
  exact Nat.find_min (firstRadiusHit_exists hω hmn) hilength ⟨by omega, hge⟩

theorem exists_head_filter_mem_take {α : Type*} (P : α → Bool)
    {l : List α} {a : α} {k : ℕ} (ha : a ∈ l.take k) (hPa : P a = true) :
    ∃ b t, l.filter P = b :: t ∧ b ∈ l.take k := by
  induction l generalizing k with
  | nil => simp at ha
  | cons c l ih =>
      cases k with
      | zero => simp at ha
      | succ k =>
          simp only [List.take_succ_cons, List.mem_cons] at ha ⊢
          by_cases hc : P c = true
          · exact ⟨c, l.filter P, by simp [hc], Or.inl rfl⟩
          · have hcfalse : P c = false := Bool.eq_false_of_not_eq_true hc
            have haTail : a ∈ l.take k := by
              rcases ha with rfl | ha
              · exact (hc hPa).elim
              · exact ha
            obtain ⟨b, t, hfilter, hb⟩ := ih haTail
            exact ⟨b, t, by simpa [hcfalse] using hfilter, Or.inr hb⟩

/-- Ordered pivotal darts along the canonical open path. -/
noncomputable def radiusPivotalDarts {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    List ((cubicGraph d).Dart) := by
  classical
  exact (canonicalRadiusWitness hω).walk.darts.filter fun a ↦
    decide (IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart a) ω)

theorem radiusPivotalDarts_nodup {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    (radiusPivotalDarts hω).Nodup := by
  classical
  exact (SimpleGraph.Walk.darts_nodup_of_support_nodup
    (canonicalRadiusWitness hω).isPath.support_nodup).filter _

/-- The finite set of edges pivotal for `Aₙ(x)`. -/
noncomputable def radiusPivotalEdgeFinset (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) : Finset (CubicEdge d) := by
  classical
  exact (cubicMetricBallEdges d x n).filter fun e ↦
    IsPivotal (radiusConnectionEvent d x n) e ω

/-- The number `N(Aₙ)` of pivotal edges. -/
noncomputable def radiusPivotalCount (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) : ℕ :=
  (radiusPivotalEdgeFinset d x n ω).card

/-- The `k`-th pivotal sausage gap, indexed from one as in Grimmett.  It is zero when `Aₙ`
does not occur or fewer than `k` pivotal edges exist. -/
noncomputable def sausageGap (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) (k : ℕ) : ℕ := by
  classical
  by_cases hω : ω ∈ radiusConnectionEvent d x n
  · let L := radiusPivotalDarts hω
    by_cases hk : 1 ≤ k ∧ k ≤ L.length
    · let a := L[k - 1]'(by omega)
      by_cases hk1 : k = 1
      · exact cubicL1Dist x a.fst
      · let b := L[k - 2]'(by omega)
        exact cubicL1Dist b.snd a.fst
    · exact n
  · exact n

theorem sausageGap_one_eq_firstPivotalDist {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n)
    (hL : 0 < (radiusPivotalDarts hω).length) :
    sausageGap d x n ω 1 =
      cubicL1Dist x ((radiusPivotalDarts hω)[0]'hL).fst := by
  classical
  unfold sausageGap
  simp only [hω, ↓reduceDIte]
  split
  next hk =>
    simp
  next hk =>
    exact (hk ⟨by omega, hL⟩).elim

theorem firstRadiusHitWalk_edge_not_pivotal_of_lt_sausageGap {d n r : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n) (hrn : r + 1 ≤ n)
    (hgap : r < sausageGap d x n ω 1) {e : CubicEdge d}
    (he : e ∈ walkEdgeFinset (firstRadiusHitWalk hω hrn)) :
    ¬IsPivotal (radiusConnectionEvent d x n) e ω := by
  classical
  intro hepiv
  have hewalk : (e : Sym2 (Cubic d)) ∈ (firstRadiusHitWalk hω hrn).edges :=
    (mem_walkEdgeFinset_iff _ _).mp he
  rw [SimpleGraph.Walk.edges] at hewalk
  obtain ⟨a, ha, hae⟩ := List.mem_map.mp hewalk
  have haedge : cubicEdgeOfDart a = e := Subtype.ext hae
  let P : (cubicGraph d).Dart → Bool := fun b ↦
    decide (IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart b) ω)
  have hPa : P a = true := by simp [P, haedge, hepiv]
  have haTake : a ∈ (canonicalRadiusWitness hω).walk.darts.take
      (firstRadiusHitIndex hω hrn) := by
    simpa [firstRadiusHitWalk, SimpleGraph.Walk.darts_take] using ha
  obtain ⟨b, t, hfilter, hb⟩ := exists_head_filter_mem_take P haTake hPa
  have hL : radiusPivotalDarts hω = b :: t := by
    simpa [radiusPivotalDarts, P] using hfilter
  have hLpos : 0 < (radiusPivotalDarts hω).length := by simp [hL]
  have hfirst : (radiusPivotalDarts hω)[0]'hLpos = b := by simp [hL]
  have hbHit : b ∈ (firstRadiusHitWalk hω hrn).darts := by
    rw [firstRadiusHitWalk, SimpleGraph.Walk.darts_take]
    exact hb
  have hbdist := firstRadiusHitWalk_dart_fst_dist_lt hω hrn hbHit
  have hgapEq := sausageGap_one_eq_firstPivotalDist hω hLpos
  rw [hfirst] at hgapEq
  omega

/-- The profile consisting of the pivotal count and all one-based sausage gaps. -/
structure PivotalSausageProfile where
  pivotalCount : ℕ
  gap : ℕ → ℕ

noncomputable def pivotalSausageProfile (d : ℕ) (x : Cubic d) (n : ℕ)
    (ω : EdgeConfiguration d) : PivotalSausageProfile where
  pivotalCount := radiusPivotalCount d x n ω
  gap := sausageGap d x n ω

theorem mem_diff_singleton_of_mem_increasingEvent_of_not_pivotal
    {ι : Type*} {A : Set (Set ι)} (hA : IsIncreasingEvent A)
    {ω : Set ι} (hω : ω ∈ A) {e : ι} (he : ¬IsPivotal A e ω) :
    ω \ {e} ∈ A := by
  by_contra hclosed
  apply he
  rw [hA.isPivotal_iff]
  exact ⟨hA (Set.subset_insert e ω) hω, hclosed⟩

/-! ### The augmented finite graph for the first-sausage BK inclusion -/

/-- Vertices of the finite augmented graph: ball vertices, a marked first-hit vertex, and a
terminal representing the outer sphere. -/
abbrev RadiusAuxVertex (d : ℕ) (x : Cubic d) (n : ℕ) :=
  Option (Option {y : Cubic d // y ∈ cubicMetricBall d x n})

def radiusAuxLattice {d n : ℕ} {x : Cubic d}
    (y : {z : Cubic d // z ∈ cubicMetricBall d x n}) : RadiusAuxVertex d x n :=
  some (some y)

def radiusAuxMark {d n : ℕ} {x : Cubic d} : RadiusAuxVertex d x n := some none

def radiusAuxSink {d n : ℕ} {x : Cubic d} : RadiusAuxVertex d x n := none

/-- One orientation of the augmented adjacency relation. `SimpleGraph.fromRel` supplies the
reverse orientations and removes loops. -/
def radiusAuxRel {d n : ℕ} {x : Cubic d} (ω : EdgeConfiguration d)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) :
    RadiusAuxVertex d x n → RadiusAuxVertex d x n → Prop
  | some (some u), some (some v) =>
      ∃ e : CubicEdge d, (e : Sym2 (Cubic d)) = s(u.1, v.1) ∧ e ∈ ω
  | some (some u), some none => u = z
  | some (some u), none => u.1 ∈ cubicMetricSphere d x n
  | some none, none => True
  | _, _ => False

def radiusAuxGraph {d n : ℕ} {x : Cubic d} (ω : EdgeConfiguration d)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) :
    SimpleGraph (RadiusAuxVertex d x n) :=
  SimpleGraph.fromRel (radiusAuxRel ω z)

theorem radiusAuxGraph_adj_lattice {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {u v : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (huv : (cubicGraph d).Adj u.1 v.1)
    (hopen : (⟨s(u.1, v.1), by rw [SimpleGraph.mem_edgeSet]; exact huv⟩ : CubicEdge d) ∈ ω) :
    (radiusAuxGraph ω z).Adj (radiusAuxLattice u) (radiusAuxLattice v) := by
  rw [radiusAuxGraph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ?_⟩
  · intro h
    have huv' : u = v := by simpa [radiusAuxLattice] using h
    exact huv.ne (congrArg Subtype.val huv')
  · exact ⟨⟨s(u.1, v.1), by rw [SimpleGraph.mem_edgeSet]; exact huv⟩, rfl, hopen⟩

theorem radiusAuxGraph_adj_mark {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) :
    (radiusAuxGraph ω z).Adj (radiusAuxLattice z) radiusAuxMark := by
  rw [radiusAuxGraph, SimpleGraph.fromRel_adj]
  simp [radiusAuxRel, radiusAuxLattice, radiusAuxMark]

theorem radiusAuxGraph_adj_sink {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (u : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (hu : u.1 ∈ cubicMetricSphere d x n) :
    (radiusAuxGraph ω z).Adj (radiusAuxLattice u) radiusAuxSink := by
  rw [radiusAuxGraph, SimpleGraph.fromRel_adj]
  simp [radiusAuxRel, radiusAuxLattice, radiusAuxSink, hu]

theorem radiusAuxGraph_adj_mark_sink {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) :
    (radiusAuxGraph ω z).Adj radiusAuxMark radiusAuxSink := by
  rw [radiusAuxGraph, SimpleGraph.fromRel_adj]
  simp [radiusAuxRel, radiusAuxMark, radiusAuxSink]

theorem nonempty_radiusAuxWalk_of_openWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    {u v : Cubic d} (hu : u ∈ cubicMetricBall d x n) (hv : v ∈ cubicMetricBall d x n)
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w)
    (hball : ∀ y ∈ w.support, y ∈ cubicMetricBall d x n) :
    Nonempty ((radiusAuxGraph ω z).Walk
      (radiusAuxLattice ⟨u, hu⟩) (radiusAuxLattice ⟨v, hv⟩)) := by
  induction w with
  | nil => exact ⟨.nil⟩
  | @cons u y v huy p ih =>
      have hy : y ∈ cubicMetricBall d x n := hball y (by simp)
      have hpopen : walkIsOpen ω p := by
        intro e he
        exact hopen e (by simp [he])
      have hpball : ∀ q ∈ p.support, q ∈ cubicMetricBall d x n := by
        intro q hq
        exact hball q (by simp [hq])
      obtain ⟨q⟩ := ih hy hv hpopen hpball
      have heopen :
          (⟨s(u, y), by rw [SimpleGraph.mem_edgeSet]; exact huy⟩ : CubicEdge d) ∈ ω :=
        hopen _ (by simp)
      exact ⟨.cons (radiusAuxGraph_adj_lattice huy heopen) q⟩

noncomputable def radiusAuxFullWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) :
    (radiusAuxGraph ω z).Walk
      (radiusAuxLattice ⟨x, by simp⟩) radiusAuxSink := by
  let W := canonicalRadiusWitness hω
  have hy : W.endpoint ∈ cubicMetricBall d x n :=
    cubicMetricSphere_subset_ball d x n W.sphere_mem
  have hball : ∀ y ∈ W.walk.support, y ∈ cubicMetricBall d x n :=
    walk_support_subset_cubicMetricBall_of_edges (by simp) W.walk W.edge_subset
  let q := Classical.choice <| nonempty_radiusAuxWalk_of_openWalk z (by simp) hy
    W.walk W.isOpen hball
  exact q.concat (radiusAuxGraph_adj_sink z ⟨W.endpoint, hy⟩ W.sphere_mem)

noncomputable def radiusAuxMarkedWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (q : (cubicGraph d).Walk x z.1) (hqopen : walkIsOpen ω q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n) :
    (radiusAuxGraph ω z).Walk
      (radiusAuxLattice ⟨x, by simp⟩) radiusAuxSink := by
  let q' := Classical.choice <| nonempty_radiusAuxWalk_of_openWalk z (by simp) z.2
    q hqopen hqball
  exact (q'.concat (radiusAuxGraph_adj_mark z)).concat (radiusAuxGraph_adj_mark_sink z)

/-- The open subgraph induced by the finite metric ball. -/
noncomputable def radiusOpenBallGraph {d n : ℕ} {x : Cubic d} (ω : EdgeConfiguration d) :
    SimpleGraph {y : Cubic d // y ∈ cubicMetricBall d x n} where
  Adj u v := ∃ e : CubicEdge d, (e : Sym2 (Cubic d)) = s(u.1, v.1) ∧ e ∈ ω
  symm := by
    rintro u v ⟨e, he, hopen⟩
    exact ⟨e, he.trans Sym2.eq_swap, hopen⟩
  loopless := ⟨by
    rintro u ⟨e, he, _⟩
    have : (cubicGraph d).Adj u.1 u.1 := by
      rw [← SimpleGraph.mem_edgeSet]
      exact he ▸ e.2
    exact (cubicGraph d).loopless.irrefl _ this⟩

abbrev RadiusTerminalVertex (d : ℕ) (x : Cubic d) (n : ℕ) :=
  Option {y : Cubic d // y ∈ cubicMetricBall d x n}

/-- Add one terminal adjacent to the outer sphere and, optionally, to a distinguished first-hit
vertex `z`. -/
def radiusTerminalRel {d n : ℕ} {x : Cubic d} (ω : EdgeConfiguration d)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) (shortcut : Prop) :
    RadiusTerminalVertex d x n → RadiusTerminalVertex d x n → Prop
  | some u, some v => (radiusOpenBallGraph ω).Adj u v
  | some u, none => u.1 ∈ cubicMetricSphere d x n ∨ (shortcut ∧ u = z)
  | none, _ => False

def radiusTerminalGraph {d n : ℕ} {x : Cubic d} (ω : EdgeConfiguration d)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) (shortcut : Prop) :
    SimpleGraph (RadiusTerminalVertex d x n) :=
  SimpleGraph.fromRel (radiusTerminalRel ω z shortcut)

theorem radiusTerminalGraph_adj_some {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    {z : {y : Cubic d // y ∈ cubicMetricBall d x n}} {shortcut : Prop}
    {u v : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (huv : (radiusOpenBallGraph ω).Adj u v) :
    (radiusTerminalGraph ω z shortcut).Adj (some u) (some v) := by
  rw [radiusTerminalGraph, SimpleGraph.fromRel_adj]
  exact ⟨by simpa using huv.ne, Or.inl huv⟩

theorem radiusTerminalGraph_adj_sink_iff {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop} {u : {y : Cubic d // y ∈ cubicMetricBall d x n}} :
    (radiusTerminalGraph ω z shortcut).Adj (some u) none ↔
      u.1 ∈ cubicMetricSphere d x n ∨ (shortcut ∧ u = z) := by
  rw [radiusTerminalGraph, SimpleGraph.fromRel_adj]
  simp [radiusTerminalRel]

theorem radiusTerminalGraph_adj_some_iff {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop} {u v : {y : Cubic d // y ∈ cubicMetricBall d x n}} :
    (radiusTerminalGraph ω z shortcut).Adj (some u) (some v) ↔
      (radiusOpenBallGraph ω).Adj u v := by
  rw [radiusTerminalGraph, SimpleGraph.fromRel_adj]
  simp only [Option.some.injEq, ne_eq, radiusTerminalRel]
  constructor
  · rintro ⟨_hne, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨by simpa using h.ne, Or.inl h⟩

theorem nonempty_radiusOpenBallWalk_of_openWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {u v : Cubic d}
    (hu : u ∈ cubicMetricBall d x n) (hv : v ∈ cubicMetricBall d x n)
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w)
    (hball : ∀ y ∈ w.support, y ∈ cubicMetricBall d x n) :
    Nonempty ((radiusOpenBallGraph ω).Walk ⟨u, hu⟩ ⟨v, hv⟩) := by
  induction w with
  | nil => exact ⟨.nil⟩
  | @cons u y v huy p ih =>
      have hy : y ∈ cubicMetricBall d x n := hball y (by simp)
      have hpopen : walkIsOpen ω p := by
        intro e he
        exact hopen e (by simp [he])
      have hpball : ∀ q ∈ p.support, q ∈ cubicMetricBall d x n := by
        intro q hq
        exact hball q (by simp [hq])
      obtain ⟨q⟩ := ih hy hv hpopen hpball
      have heopen :
          (⟨s(u, y), by rw [SimpleGraph.mem_edgeSet]; exact huy⟩ : CubicEdge d) ∈ ω :=
        hopen _ (by simp)
      have hxy : (radiusOpenBallGraph ω).Adj ⟨u, hu⟩ ⟨y, hy⟩ :=
        ⟨⟨s(u, y), by rw [SimpleGraph.mem_edgeSet]; exact huy⟩, rfl, heopen⟩
      exact ⟨.cons hxy q⟩

structure RadiusOpenBallWalkLift {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    {u v : Cubic d} (hu : u ∈ cubicMetricBall d x n) (hv : v ∈ cubicMetricBall d x n)
    (w : (cubicGraph d).Walk u v) where
  walk : (radiusOpenBallGraph ω).Walk ⟨u, hu⟩ ⟨v, hv⟩
  map_edges : walk.edges.map (Sym2.map Subtype.val) = w.edges

theorem nonempty_radiusOpenBallWalkLift {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {u v : Cubic d}
    (hu : u ∈ cubicMetricBall d x n) (hv : v ∈ cubicMetricBall d x n)
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w)
    (hball : ∀ y ∈ w.support, y ∈ cubicMetricBall d x n) :
    Nonempty (RadiusOpenBallWalkLift (ω := ω) hu hv w) := by
  induction w with
  | nil => exact ⟨⟨.nil, by simp⟩⟩
  | @cons u y v huy p ih =>
      have hy : y ∈ cubicMetricBall d x n := hball y (by simp)
      have hpopen : walkIsOpen ω p := by
        intro e he
        exact hopen e (by simp [he])
      have hpball : ∀ q ∈ p.support, q ∈ cubicMetricBall d x n := by
        intro q hq
        exact hball q (by simp [hq])
      obtain ⟨Q⟩ := ih hy hv hpopen hpball
      have heopen :
          (⟨s(u, y), by rw [SimpleGraph.mem_edgeSet]; exact huy⟩ : CubicEdge d) ∈ ω :=
        hopen _ (by simp)
      have hxy : (radiusOpenBallGraph ω).Adj ⟨u, hu⟩ ⟨y, hy⟩ :=
        ⟨⟨s(u, y), by rw [SimpleGraph.mem_edgeSet]; exact huy⟩, rfl, heopen⟩
      exact ⟨⟨.cons hxy Q.walk, by simp [Q.map_edges]⟩⟩

noncomputable def radiusOpenBallWalkLiftOf {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {u v : Cubic d}
    (hu : u ∈ cubicMetricBall d x n) (hv : v ∈ cubicMetricBall d x n)
    (w : (cubicGraph d).Walk u v) (hopen : walkIsOpen ω w)
    (hball : ∀ y ∈ w.support, y ∈ cubicMetricBall d x n) :
    RadiusOpenBallWalkLift (ω := ω) hu hv w :=
  Classical.choice (nonempty_radiusOpenBallWalkLift hu hv w hopen hball)

def radiusTerminalNonSink {d n : ℕ} {x : Cubic d} :
    Set (RadiusTerminalVertex d x n) := {a | a ≠ none}

noncomputable def radiusTerminalGet {d n : ℕ} {x : Cubic d}
    (a : radiusTerminalNonSink (d := d) (n := n) (x := x)) :
    {y : Cubic d // y ∈ cubicMetricBall d x n} :=
  a.1.get (Option.isSome_iff_ne_none.mpr a.2)

@[simp]
theorem radiusTerminalGet_some {d n : ℕ} {x : Cubic d}
    (u : {y : Cubic d // y ∈ cubicMetricBall d x n}) :
    radiusTerminalGet (⟨some u, Option.some_ne_none u⟩ :
      radiusTerminalNonSink (d := d) (n := n) (x := x)) = u := by
  rfl

noncomputable def radiusTerminalNonSinkHom {d n : ℕ} {x : Cubic d}
    (ω : EdgeConfiguration d) (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (shortcut : Prop) :
    (radiusTerminalGraph ω z shortcut).induce
        (radiusTerminalNonSink (d := d) (n := n) (x := x)) →g
      radiusOpenBallGraph (d := d) (n := n) (x := x) ω where
  toFun := radiusTerminalGet
  map_rel' := by
    intro a b hab
    have hab' : (radiusTerminalGraph ω z shortcut).Adj a.1 b.1 :=
      SimpleGraph.induce_adj.mp hab
    have ha := Option.some_get (Option.isSome_iff_ne_none.mpr a.2)
    have hb := Option.some_get (Option.isSome_iff_ne_none.mpr b.2)
    rw [← ha, ← hb] at hab'
    exact radiusTerminalGraph_adj_some_iff.mp hab'

noncomputable def projectRadiusTerminalWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop} {u v : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (p : (radiusTerminalGraph ω z shortcut).Walk (some u) (some v))
    (hnone : none ∉ p.support) : (radiusOpenBallGraph ω).Walk u v := by
  have hall : ∀ a ∈ p.support, a ∈ radiusTerminalNonSink := by
    intro a ha
    exact fun h ↦ hnone (h ▸ ha)
  exact ((p.induce radiusTerminalNonSink hall).map
    (radiusTerminalNonSinkHom ω z shortcut)).copy
      (by simp [radiusTerminalNonSinkHom]) (by simp [radiusTerminalNonSinkHom])

theorem map_projectRadiusTerminalWalk_edges {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop} {u v : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (p : (radiusTerminalGraph ω z shortcut).Walk (some u) (some v))
    (hnone : none ∉ p.support) :
    (projectRadiusTerminalWalk p hnone).edges.map (Sym2.map some) = p.edges := by
  have hall : ∀ a ∈ p.support, a ∈ radiusTerminalNonSink := by
    intro a ha
    exact fun h ↦ hnone (h ▸ ha)
  let q := p.induce radiusTerminalNonSink hall
  have hind : (q.map (SimpleGraph.Embedding.induce radiusTerminalNonSink).toHom).edges =
      p.edges := by
    exact congrArg SimpleGraph.Walk.edges (SimpleGraph.Walk.map_induce p hall)
  have hget : ∀ a : radiusTerminalNonSink (d := d) (n := n) (x := x),
      some (radiusTerminalGet a) = a.1 := by
    intro a
    exact Option.some_get _
  calc
    (projectRadiusTerminalWalk p hnone).edges.map (Sym2.map some) =
        (q.map (radiusTerminalNonSinkHom ω z shortcut)).edges.map (Sym2.map some) := by
      simp [projectRadiusTerminalWalk, q]
    _ = q.edges.map (Sym2.map (fun a ↦ some (radiusTerminalGet a))) := by
      simp [SimpleGraph.Walk.edges_map, List.map_map, Sym2.map_map,
        radiusTerminalNonSinkHom, Function.comp_def]
    _ = q.edges.map (Sym2.map (fun a ↦ a.1)) := by
      apply List.map_congr_left
      intro e _he
      apply Sym2.map_congr
      intro a _ha
      exact hget a
    _ = p.edges := by
      rw [SimpleGraph.Walk.edges_map] at hind
      exact hind

def radiusOpenBallToTerminalHom {d n : ℕ} {x : Cubic d}
    (ω : EdgeConfiguration d) (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (shortcut : Prop) :
    radiusOpenBallGraph (d := d) (n := n) (x := x) ω →g
      radiusTerminalGraph ω z shortcut where
  toFun := some
  map_rel' := radiusTerminalGraph_adj_some

noncomputable def canonicalRadiusOpenBallLift {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    RadiusOpenBallWalkLift (ω := ω) (x := x) (n := n) (by simp)
      (cubicMetricSphere_subset_ball d x n (canonicalRadiusWitness hω).sphere_mem)
      (canonicalRadiusWitness hω).walk :=
  radiusOpenBallWalkLiftOf (ω := ω) (by simp)
    (cubicMetricSphere_subset_ball d x n (canonicalRadiusWitness hω).sphere_mem)
    (canonicalRadiusWitness hω).walk (canonicalRadiusWitness hω).isOpen
    (walk_support_subset_cubicMetricBall_of_edges (by simp)
      (canonicalRadiusWitness hω).walk (canonicalRadiusWitness hω).edge_subset)

noncomputable def canonicalRadiusOpenBallLiftOfSubset {d n : ℕ} {x : Cubic d}
    {η ω : EdgeConfiguration d} (hηω : η ⊆ ω)
    (hη : η ∈ radiusConnectionEvent d x n) :
    RadiusOpenBallWalkLift (ω := ω) (x := x) (n := n) (by simp)
      (cubicMetricSphere_subset_ball d x n (canonicalRadiusWitness hη).sphere_mem)
      (canonicalRadiusWitness hη).walk :=
  radiusOpenBallWalkLiftOf (ω := ω) (by simp)
    (cubicMetricSphere_subset_ball d x n (canonicalRadiusWitness hη).sphere_mem)
    (canonicalRadiusWitness hη).walk
    (fun e he ↦ hηω ((canonicalRadiusWitness hη).isOpen e he))
    (walk_support_subset_cubicMetricBall_of_edges (by simp)
      (canonicalRadiusWitness hη).walk (canonicalRadiusWitness hη).edge_subset)

noncomputable def radiusTerminalFullWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) (shortcut : Prop) :
    (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none :=
  ((canonicalRadiusOpenBallLift hω).walk.map
      (radiusOpenBallToTerminalHom ω z shortcut)).concat
    (radiusTerminalGraph_adj_sink_iff.mpr
      (Or.inl (canonicalRadiusWitness hω).sphere_mem))

noncomputable def radiusTerminalFullWalkOfSubset {d n : ℕ} {x : Cubic d}
    {η ω : EdgeConfiguration d} (hηω : η ⊆ ω)
    (hη : η ∈ radiusConnectionEvent d x n)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n}) (shortcut : Prop) :
    (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none :=
  ((canonicalRadiusOpenBallLiftOfSubset hηω hη).walk.map
      (radiusOpenBallToTerminalHom ω z shortcut)).concat
    (radiusTerminalGraph_adj_sink_iff.mpr
      (Or.inl (canonicalRadiusWitness hη).sphere_mem))

noncomputable def radiusPrefixOpenBallLift {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (q : (cubicGraph d).Walk x z.1) (hqopen : walkIsOpen ω q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n) :
    RadiusOpenBallWalkLift (ω := ω) (by simp) z.2 q :=
  radiusOpenBallWalkLiftOf (ω := ω) (by simp) z.2 q hqopen hqball

noncomputable def radiusTerminalShortcutWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (q : (cubicGraph d).Walk x z.1) (hqopen : walkIsOpen ω q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n) :
    (radiusTerminalGraph ω z True).Walk (some ⟨x, by simp⟩) none :=
  ((radiusPrefixOpenBallLift z q hqopen hqball).walk.map
      (radiusOpenBallToTerminalHom ω z True)).concat
    (radiusTerminalGraph_adj_sink_iff.mpr (Or.inr ⟨True.intro, rfl⟩))

structure RadiusTerminalProjection {d n : ℕ} {x : Cubic d}
    (ω : EdgeConfiguration d) (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (shortcut : Prop)
    (p : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none) where
  endpoint : {y : Cubic d // y ∈ cubicMetricBall d x n}
  terminal_kind : endpoint.1 ∈ cubicMetricSphere d x n ∨ (shortcut ∧ endpoint = z)
  walk : (radiusOpenBallGraph ω).Walk ⟨x, by simp⟩ endpoint
  edge_subset : ∀ e ∈ walk.edges, Sym2.map some e ∈ p.edges
  last_edge_mem : s(some endpoint, none) ∈ p.edges

noncomputable def radiusTerminalProjectionOfPath {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop}
    (p : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none)
    (hp : p.IsPath) : RadiusTerminalProjection ω z shortcut p := by
  have hnil : ¬p.Nil := by
    intro h
    exact Option.some_ne_none
      (⟨x, by simp⟩ : {y : Cubic d // y ∈ cubicMetricBall d x n}) h.eq
  have hadj := p.adj_penultimate hnil
  cases hpen : p.penultimate with
  | none =>
      exact (hadj.ne (by simp [hpen])).elim
  | some u =>
      let r : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) (some u) :=
        p.dropLast.copy rfl hpen
      have hnodup : (p.dropLast.support ++ [none]).Nodup := by
        rw [p.support_dropLast_concat hnil]
        exact hp.support_nodup
      have hnoneDrop : none ∉ p.dropLast.support := by
        have h := (List.nodup_append.mp hnodup).2.2
        exact fun hmem ↦ h none hmem none (by simp) rfl
      have hnone : none ∉ r.support := by
        simpa [r] using hnoneDrop
      let q := projectRadiusTerminalWalk r hnone
      refine ⟨u, ?_, q, ?_, ?_⟩
      · apply radiusTerminalGraph_adj_sink_iff.mp
        simpa [hpen] using hadj
      · intro e heq
        have heR : Sym2.map some e ∈ r.edges := by
          rw [← map_projectRadiusTerminalWalk_edges r hnone]
          exact List.mem_map.mpr ⟨e, heq, rfl⟩
        have heDrop : Sym2.map some e ∈ p.dropLast.edges := by
          simpa [r] using heR
        exact (SimpleGraph.Walk.isSubwalk_take p (p.length - 1)).edges_subset heDrop
      · simpa [hpen] using p.mk_penultimate_end_mem_edges hnil

def radiusOpenBallToCubicHom {d n : ℕ} {x : Cubic d} (ω : EdgeConfiguration d) :
    radiusOpenBallGraph (d := d) (n := n) (x := x) ω →g cubicGraph d where
  toFun := Subtype.val
  map_rel' := by
    rintro u v ⟨e, he, _hopen⟩
    rw [← SimpleGraph.mem_edgeSet]
    exact he ▸ e.2

theorem walkIsOpen_map_radiusOpenBallToCubicHom {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {u v : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (q : (radiusOpenBallGraph ω).Walk u v) :
    walkIsOpen ω (q.map (radiusOpenBallToCubicHom ω)) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
  induction f using Sym2.inductionOn with
  | _ a b =>
      have hadj : (radiusOpenBallGraph ω).Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact q.edges_subset_edgeSet hf
      obtain ⟨g, hg, hgopen⟩ := hadj
      have hval : e = (g : Sym2 (Cubic d)) := by
        exact hfe.symm.trans hg.symm
      simpa [edgeOpen, hval] using hgopen

theorem walkIsOpen_walkEdgeFinset {d : ℕ} {u v : Cubic d}
    (q : (cubicGraph d).Walk u v) : walkIsOpen (walkEdgeFinset q : Set (CubicEdge d)) q := by
  intro e he
  exact (mem_walkEdgeFinset_iff q ⟨e, q.edges_subset_edgeSet he⟩).mpr he

noncomputable def RadiusTerminalProjection.cubicWalk {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop} {p : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none}
    (P : RadiusTerminalProjection ω z shortcut p) :
    (cubicGraph d).Walk x P.endpoint.1 :=
  P.walk.map (radiusOpenBallToCubicHom ω)

noncomputable def RadiusTerminalProjection.edgeFinset {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop} {p : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none}
    (P : RadiusTerminalProjection ω z shortcut p) : Finset (CubicEdge d) :=
  walkEdgeFinset P.cubicWalk

theorem RadiusTerminalProjection.edgeFinset_subset {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop} {p : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none}
    (P : RadiusTerminalProjection ω z shortcut p) : (P.edgeFinset : Set (CubicEdge d)) ⊆ ω := by
  intro e he
  have he' : (e : Sym2 (Cubic d)) ∈ P.cubicWalk.edges :=
    (mem_walkEdgeFinset_iff P.cubicWalk e).mp he
  exact walkIsOpen_map_radiusOpenBallToCubicHom P.walk e.1 he'

theorem RadiusTerminalProjection.edgeFinset_mem_radiusConnectionEvent {d n m : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    {z : {y : Cubic d // y ∈ cubicMetricBall d x n}} {shortcut : Prop}
    {p : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none}
    (P : RadiusTerminalProjection ω z shortcut p)
    (hm : m ≤ cubicL1Dist x P.endpoint.1) :
    (P.edgeFinset : Set (CubicEdge d)) ∈ radiusConnectionEvent d x m := by
  exact exists_open_walk_to_cubicMetricSphere_in_ball P.cubicWalk
    (walkIsOpen_walkEdgeFinset P.cubicWalk) hm

theorem radiusTerminalProjection_edgeFinset_disjoint {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    {shortcut : Prop}
    {p q : (radiusTerminalGraph ω z shortcut).Walk (some ⟨x, by simp⟩) none}
    (P : RadiusTerminalProjection ω z shortcut p)
    (Q : RadiusTerminalProjection ω z shortcut q)
    (hpq : p.edges.Disjoint q.edges) : Disjoint P.edgeFinset Q.edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heP heQ
  have hePc : (e : Sym2 (Cubic d)) ∈ P.cubicWalk.edges :=
    (mem_walkEdgeFinset_iff P.cubicWalk e).mp heP
  have heQc : (e : Sym2 (Cubic d)) ∈ Q.cubicWalk.edges :=
    (mem_walkEdgeFinset_iff Q.cubicWalk e).mp heQ
  change (e : Sym2 (Cubic d)) ∈
    (P.walk.map (radiusOpenBallToCubicHom ω)).edges at hePc
  change (e : Sym2 (Cubic d)) ∈
    (Q.walk.map (radiusOpenBallToCubicHom ω)).edges at heQc
  rw [SimpleGraph.Walk.edges_map] at hePc heQc
  obtain ⟨f, hfP, hfeP⟩ := List.mem_map.mp hePc
  obtain ⟨g, hgQ, hgeQ⟩ := List.mem_map.mp heQc
  have hfg : f = g := by
    apply Sym2.map.injective Subtype.val_injective
    exact hfeP.trans hgeQ.symm
  subst g
  exact List.disjoint_left.mp hpq (P.edge_subset f hfP) (Q.edge_subset f hgQ)

theorem mem_openWitnessDisjointOccurrence_of_terminal_paths {d n m : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (hz : z.1 ∈ cubicMetricSphere d x m) (hmn : m ≤ n)
    {p q : (radiusTerminalGraph ω z True).Walk (some ⟨x, by simp⟩) none}
    (hp : p.IsPath) (hq : q.IsPath) (hpq : p.edges.Disjoint q.edges) :
    ω ∈ OpenWitnessDisjointOccurrence
      (radiusConnectionEvent d x m) (radiusConnectionEvent d x n) := by
  let P := radiusTerminalProjectionOfPath p hp
  let Q := radiusTerminalProjectionOfPath q hq
  have hfinDisj : Disjoint P.edgeFinset Q.edgeFinset :=
    radiusTerminalProjection_edgeFinset_disjoint P Q hpq
  have hnotBothShortcut :
      ¬((True ∧ P.endpoint = z) ∧ (True ∧ Q.endpoint = z)) := by
    rintro ⟨⟨_, hPz⟩, ⟨_, hQz⟩⟩
    have heP : s(some z, none) ∈ p.edges := by simpa [P, hPz] using P.last_edge_mem
    have heQ : s(some z, none) ∈ q.edges := by simpa [Q, hQz] using Q.last_edge_mem
    exact List.disjoint_left.mp hpq heP heQ
  have event_of_projection
      {r : (radiusTerminalGraph ω z True).Walk (some ⟨x, by simp⟩) none}
      (R : RadiusTerminalProjection ω z True r)
      (hkind : R.endpoint.1 ∈ cubicMetricSphere d x n ∨ (True ∧ R.endpoint = z)) :
      (R.edgeFinset : Set (CubicEdge d)) ∈ radiusConnectionEvent d x m := by
    apply R.edgeFinset_mem_radiusConnectionEvent
    rcases hkind with hsphere | ⟨_, hrz⟩
    · rw [mem_cubicMetricSphere_iff_l1Dist_eq] at hsphere
      omega
    · rw [hrz]
      rw [mem_cubicMetricSphere_iff_l1Dist_eq] at hz
      omega
  rcases P.terminal_kind with hPsphere | hPshortcut
  · have hPn : (P.edgeFinset : Set (CubicEdge d)) ∈ radiusConnectionEvent d x n := by
      apply P.edgeFinset_mem_radiusConnectionEvent
      exact (mem_cubicMetricSphere_iff_l1Dist_eq.mp hPsphere).ge
    have hQm : (Q.edgeFinset : Set (CubicEdge d)) ∈ radiusConnectionEvent d x m := by
      exact event_of_projection Q Q.terminal_kind
    exact ⟨Q.edgeFinset, P.edgeFinset, hfinDisj.symm, Q.edgeFinset_subset,
      P.edgeFinset_subset, hQm, hPn⟩
  · have hQsphere : Q.endpoint.1 ∈ cubicMetricSphere d x n := by
      rcases Q.terminal_kind with h | h
      · exact h
      · exact (hnotBothShortcut ⟨hPshortcut, h⟩).elim
    have hQn : (Q.edgeFinset : Set (CubicEdge d)) ∈ radiusConnectionEvent d x n := by
      apply Q.edgeFinset_mem_radiusConnectionEvent
      exact (mem_cubicMetricSphere_iff_l1Dist_eq.mp hQsphere).ge
    have hPm : (P.edgeFinset : Set (CubicEdge d)) ∈ radiusConnectionEvent d x m := by
      exact event_of_projection P P.terminal_kind
    exact ⟨P.edgeFinset, Q.edgeFinset, hfinDisj, P.edgeFinset_subset,
      Q.edgeFinset_subset, hPm, hQn⟩

theorem mem_openWitnessDisjointOccurrence_of_terminal_overlap_avoidance
    {d n m : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    {z : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (hz : z.1 ∈ cubicMetricSphere d x m) (hmn : m ≤ n)
    (full shortcut : (radiusTerminalGraph ω z True).Walk (some ⟨x, by simp⟩) none)
    (havoid : ∀ e, e ∈ full.edges → e ∈ shortcut.edges →
      ∃ r : (radiusTerminalGraph ω z True).Walk (some ⟨x, by simp⟩) none,
        e ∉ r.edges) :
    ω ∈ OpenWitnessDisjointOccurrence
      (radiusConnectionEvent d x m) (radiusConnectionEvent d x n) := by
  classical
  have hreach : (radiusTerminalGraph ω z True).IsEdgeReachable 2
      (some ⟨x, by simp⟩) none :=
    TwoEdgeMenger.isEdgeReachable_two_of_walks_and_overlap_avoidance
      full shortcut havoid
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    TwoEdgeMenger.exists_two_edgeDisjoint_paths_of_isEdgeReachable_two hreach
  exact mem_openWitnessDisjointOccurrence_of_terminal_paths hz hmn hp hq hpq

theorem radiusTerminal_shortcut_edge_not_mem_full {d n m : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (hz : z.1 ∈ cubicMetricSphere d x m) (hmn : m < n) :
    s((some z : RadiusTerminalVertex d x n), none) ∉
      (radiusTerminalFullWalk hω z True).edges := by
  intro he
  unfold radiusTerminalFullWalk at he
  change s((some z : RadiusTerminalVertex d x n), none) ∈
    (((canonicalRadiusOpenBallLift hω).walk.map
      (radiusOpenBallToTerminalHom ω z True)).concat
        (radiusTerminalGraph_adj_sink_iff.mpr
          (Or.inl (canonicalRadiusWitness hω).sphere_mem))).edges at he
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
  simp only [List.mem_singleton] at he
  rcases he with he | heq
  · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e, _he, heq⟩ := he
    change Sym2.map some e =
      s((some z : RadiusTerminalVertex d x n), none) at heq
    have hsink : none ∈ s((some z : RadiusTerminalVertex d x n), none) := by simp
    rw [← heq] at hsink
    simp at hsink
  · have hendpoint : z.1 = (canonicalRadiusWitness hω).endpoint := by
      change s((some z : RadiusTerminalVertex d x n), none) =
        s(some ⟨(canonicalRadiusWitness hω).endpoint,
          cubicMetricSphere_subset_ball d x n (canonicalRadiusWitness hω).sphere_mem⟩,
          none) at heq
      rcases Sym2.eq_iff.mp heq with h | h
      · exact congrArg Subtype.val (Option.some.inj h.1)
      · exact (Option.some_ne_none z h.1).elim
    have hzm := mem_cubicMetricSphere_iff_l1Dist_eq.mp hz
    have hzn := mem_cubicMetricSphere_iff_l1Dist_eq.mp
      (canonicalRadiusWitness hω).sphere_mem
    rw [hendpoint] at hzm
    omega

theorem exists_prefixBallEdge_of_mem_terminalFull_and_shortcut {d n m : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (hz : z.1 ∈ cubicMetricSphere d x m) (hmn : m < n)
    (q : (cubicGraph d).Walk x z.1) (hqopen : walkIsOpen ω q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n)
    (e : Sym2 (RadiusTerminalVertex d x n))
    (heFull : e ∈ (radiusTerminalFullWalk hω z True).edges)
    (heShortcut : e ∈ (radiusTerminalShortcutWalk z q hqopen hqball).edges) :
    ∃ f ∈ (radiusPrefixOpenBallLift z q hqopen hqball).walk.edges,
      e = Sym2.map some f := by
  unfold radiusTerminalShortcutWalk at heShortcut
  change e ∈
    (((radiusPrefixOpenBallLift z q hqopen hqball).walk.map
      (radiusOpenBallToTerminalHom ω z True)).concat
        (radiusTerminalGraph_adj_sink_iff.mpr (Or.inr ⟨True.intro, rfl⟩))).edges
      at heShortcut
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at heShortcut
  simp only [List.mem_singleton] at heShortcut
  rcases heShortcut with he | he
  · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨f, hf, hfe⟩ := he
    refine ⟨f, hf, ?_⟩
    change Sym2.map some f = e at hfe
    exact hfe.symm
  · exfalso
    change e = s((some z : RadiusTerminalVertex d x n), none) at he
    apply radiusTerminal_shortcut_edge_not_mem_full hω z hz hmn
    rw [← he]
    exact heFull

theorem mapped_prefixBallEdge_not_mem_terminalFullOfSubset {d n : ℕ}
    {x : Cubic d} {η ω : EdgeConfiguration d} (hηω : η ⊆ ω)
    (hη : η ∈ radiusConnectionEvent d x n)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (q : (cubicGraph d).Walk x z.1) (hqopen : walkIsOpen ω q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n)
    (f : Sym2 {y : Cubic d // y ∈ cubicMetricBall d x n})
    (hf : f ∈ (radiusPrefixOpenBallLift z q hqopen hqball).walk.edges)
    (heclosed :
      (⟨Sym2.map Subtype.val f, by
        apply q.edges_subset_edgeSet
        rw [← (radiusPrefixOpenBallLift z q hqopen hqball).map_edges]
        exact List.mem_map.mpr ⟨f, hf, rfl⟩⟩ : CubicEdge d) ∉ η) :
    Sym2.map some f ∉ (radiusTerminalFullWalkOfSubset hηω hη z True).edges := by
  intro he
  unfold radiusTerminalFullWalkOfSubset at he
  change Sym2.map some f ∈
    (((canonicalRadiusOpenBallLiftOfSubset hηω hη).walk.map
      (radiusOpenBallToTerminalHom ω z True)).concat
        (radiusTerminalGraph_adj_sink_iff.mpr
          (Or.inl (canonicalRadiusWitness hη).sphere_mem))).edges at he
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at he
  simp only [List.mem_singleton] at he
  rcases he with he | he
  · rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨g, hg, hgf⟩ := he
    change Sym2.map some g = Sym2.map some f at hgf
    have hfg : f = g := (Sym2.map.injective (Option.some_injective _)) hgf.symm
    subst g
    have hfW : Sym2.map Subtype.val f ∈ (canonicalRadiusWitness hη).walk.edges := by
      rw [← (canonicalRadiusOpenBallLiftOfSubset hηω hη).map_edges]
      exact List.mem_map.mpr ⟨f, hg, rfl⟩
    exact heclosed ((canonicalRadiusWitness hη).isOpen _ hfW)
  · have hsink : none ∈ Sym2.map some f := by
      rw [he]
      simp
    simp at hsink

theorem mem_openWitnessDisjointOccurrence_of_nonpivotal_prefix {d n m : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    (z : {y : Cubic d // y ∈ cubicMetricBall d x n})
    (hz : z.1 ∈ cubicMetricSphere d x m) (hmn : m < n)
    (q : (cubicGraph d).Walk x z.1) (hqopen : walkIsOpen ω q)
    (hqball : ∀ y ∈ q.support, y ∈ cubicMetricBall d x n)
    (hnonpiv : ∀ e ∈ walkEdgeFinset q,
      ¬IsPivotal (radiusConnectionEvent d x n) e ω) :
    ω ∈ OpenWitnessDisjointOccurrence
      (radiusConnectionEvent d x m) (radiusConnectionEvent d x n) := by
  let full := radiusTerminalFullWalk hω z True
  let shortcut := radiusTerminalShortcutWalk z q hqopen hqball
  apply mem_openWitnessDisjointOccurrence_of_terminal_overlap_avoidance hz hmn.le
    full shortcut
  intro e heFull heShortcut
  obtain ⟨f, hf, hef⟩ := exists_prefixBallEdge_of_mem_terminalFull_and_shortcut
    hω z hz hmn q hqopen hqball e heFull heShortcut
  let ef : CubicEdge d := ⟨Sym2.map Subtype.val f, by
    apply q.edges_subset_edgeSet
    rw [← (radiusPrefixOpenBallLift z q hqopen hqball).map_edges]
    exact List.mem_map.mpr ⟨f, hf, rfl⟩⟩
  have hefq : ef ∈ walkEdgeFinset q := by
    rw [mem_walkEdgeFinset_iff]
    exact (radiusPrefixOpenBallLift z q hqopen hqball).map_edges ▸
      List.mem_map.mpr ⟨f, hf, rfl⟩
  have hclosed : ω \ {ef} ∈ radiusConnectionEvent d x n :=
    mem_diff_singleton_of_mem_increasingEvent_of_not_pivotal
      (isIncreasingEvent_radiusConnectionEvent d x n) hω (hnonpiv ef hefq)
  refine ⟨radiusTerminalFullWalkOfSubset Set.diff_subset hclosed z True, ?_⟩
  rw [hef]
  apply mapped_prefixBallEdge_not_mem_terminalFullOfSubset Set.diff_subset hclosed
    z q hqopen hqball f hf
  simp [ef]

/-- Grimmett's deterministic inclusion (5.14): if the first sausage is longer than `r`,
`A_{r+1}` and `A_n` have disjoint open witnesses. -/
theorem firstSausageLong_mem_disjointOccurrence_of_lt {d n r : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n) (hrn : r + 1 < n)
    (hgap : r < sausageGap d x n ω 1) :
    ω ∈ OpenWitnessDisjointOccurrence
      (radiusConnectionEvent d x (r + 1)) (radiusConnectionEvent d x n) := by
  let hrnle : r + 1 ≤ n := hrn.le
  let y := (canonicalRadiusWitness hω).walk.getVert (firstRadiusHitIndex hω hrnle)
  have hydist : cubicL1Dist x y = r + 1 := by
    simpa [y] using firstRadiusHit_dist_eq hω hrnle
  have hyball : y ∈ cubicMetricBall d x n := by
    rw [mem_cubicMetricBall_iff_l1Dist_le, hydist]
    exact hrnle
  let z : {q : Cubic d // q ∈ cubicMetricBall d x n} := ⟨y, hyball⟩
  let q := firstRadiusHitWalk hω hrnle
  have hz : z.1 ∈ cubicMetricSphere d x (r + 1) := by
    rw [mem_cubicMetricSphere_iff_l1Dist_eq]
    exact hydist
  have hqopen : walkIsOpen ω q := by
    exact walkIsOpen_take (canonicalRadiusWitness hω).walk
      (canonicalRadiusWitness hω).isOpen (firstRadiusHitIndex hω hrnle)
  have hWball : ∀ a ∈ (canonicalRadiusWitness hω).walk.support,
      a ∈ cubicMetricBall d x n :=
    walk_support_subset_cubicMetricBall_of_edges (by simp)
      (canonicalRadiusWitness hω).walk (canonicalRadiusWitness hω).edge_subset
  have hqball : ∀ a ∈ q.support, a ∈ cubicMetricBall d x n := by
    intro a ha
    exact hWball a ((SimpleGraph.Walk.isSubwalk_take
      (canonicalRadiusWitness hω).walk (firstRadiusHitIndex hω hrn.le)).support_subset ha)
  apply mem_openWitnessDisjointOccurrence_of_nonpivotal_prefix hω z hz (by omega)
    q hqopen hqball
  intro e he
  exact firstRadiusHitWalk_edge_not_pivotal_of_lt_sausageGap hω hrnle hgap he

def firstSausageLongEvent (d : ℕ) (x : Cubic d) (n r : ℕ) :
    Set (EdgeConfiguration d) :=
  {ω | ω ∈ radiusConnectionEvent d x n ∧ r < sausageGap d x n ω 1}

def firstSausageShortEvent (d : ℕ) (x : Cubic d) (n r : ℕ) :
    Set (EdgeConfiguration d) :=
  {ω | ω ∈ radiusConnectionEvent d x n ∧ sausageGap d x n ω 1 ≤ r}

/-- The probability form of (5.14), obtained from the deterministic inclusion and BK. -/
theorem firstSausageLong_probability_le_of_lt {d n r : ℕ}
    (p : I) (hrn : r + 1 < n) :
    (bernoulliBondMeasure d p).real (firstSausageLongEvent d cubicOrigin n r) ≤
      radiusTail d p (r + 1) * radiusTail d p n := by
  calc
    (bernoulliBondMeasure d p).real (firstSausageLongEvent d cubicOrigin n r) ≤
        (bernoulliBondMeasure d p).real (OpenWitnessDisjointOccurrence
          (radiusConnectionEvent d cubicOrigin (r + 1))
          (radiusConnectionEvent d cubicOrigin n)) := by
      apply measureReal_mono
      intro ω hω
      exact firstSausageLong_mem_disjointOccurrence_of_lt hω.1 hrn hω.2
      exact MeasureTheory.measure_ne_top _ _
    _ ≤ (bernoulliBondMeasure d p).real
          (radiusConnectionEvent d cubicOrigin (r + 1)) *
        (bernoulliBondMeasure d p).real (radiusConnectionEvent d cubicOrigin n) :=
      bernoulliBondMeasure_real_disjointOccurrence_le_mul p
        (isIncreasingEvent_radiusConnectionEvent d cubicOrigin (r + 1))
        (isIncreasingEvent_radiusConnectionEvent d cubicOrigin n)
        (dependsOn_radiusConnectionEvent d cubicOrigin (r + 1))
        (dependsOn_radiusConnectionEvent d cubicOrigin n)
    _ = radiusTail d p (r + 1) * radiusTail d p n := by
      rfl

theorem pivotal_open_of_mem_event {ι : Type*} {A : Set (Set ι)}
    (hA : IsIncreasingEvent A) {ω : Set ι} (hω : ω ∈ A) {e : ι}
    (he : IsPivotal A e ω) : e ∈ ω := by
  have hpiv := (hA.isPivotal_iff e ω).mp he
  by_contra heω
  apply hpiv.2
  simpa [Set.diff_singleton_eq_self heω] using hω

/-- Every pivotal edge of `Aₙ(x)` occurs on every open path witnessing `Aₙ(x)`. -/
theorem pivotal_mem_witness_walk {d n : ℕ} {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n)
    {y : Cubic d} (hy : y ∈ cubicMetricSphere d x n)
    (w : (cubicGraph d).Walk x y) (hopen : walkIsOpen ω w)
    (hsub : walkEdgeFinset w ⊆ cubicMetricBallEdges d x n)
    {e : CubicEdge d} (he : IsPivotal (radiusConnectionEvent d x n) e ω) :
    (e : Sym2 (Cubic d)) ∈ w.edges := by
  have heopen := pivotal_open_of_mem_event
    (isIncreasingEvent_radiusConnectionEvent d x n) hω he
  by_contra hew
  have hopen' : walkIsOpen (ω \ {e}) w := by
    intro f hf
    have hfopen := hopen f hf
    constructor
    · exact hfopen
    · intro hfe
      apply hew
      have hval : f = (e : Sym2 (Cubic d)) := by
        exact congrArg Subtype.val (by simpa using hfe)
      exact hval ▸ hf
  have hclosed : ω \ {e} ∈ radiusConnectionEvent d x n :=
    ⟨y, hy, w, hopen', hsub⟩
  exact ((isIncreasingEvent_radiusConnectionEvent d x n).isPivotal_iff e ω).mp he |>.2 hclosed

/-- The canonical pivotal list contains exactly the pivotal edges of `Aₙ(x)`; in particular,
the pivotal count does not omit any pivotal edge. -/
theorem mem_radiusPivotalDarts_iff {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n)
    (a : (cubicGraph d).Dart) :
    a ∈ radiusPivotalDarts hω ↔
      a ∈ (canonicalRadiusWitness hω).walk.darts ∧
        IsPivotal (radiusConnectionEvent d x n) (cubicEdgeOfDart a) ω := by
  classical
  simp [radiusPivotalDarts]

theorem radiusPivotalDarts_length_eq_count {d n : ℕ} {x : Cubic d}
    {ω : EdgeConfiguration d} (hω : ω ∈ radiusConnectionEvent d x n) :
    (radiusPivotalDarts hω).length = radiusPivotalCount d x n ω := by
  classical
  let w := (canonicalRadiusWitness hω).walk
  let L := radiusPivotalDarts hω
  have hLsub : ∀ a ∈ L, a ∈ w.darts := by
    intro a ha
    exact (mem_radiusPivotalDarts_iff hω a).mp ha |>.1
  have hedge_inj : ∀ a ∈ w.darts, ∀ b ∈ w.darts,
      cubicEdgeOfDart a = cubicEdgeOfDart b → a = b := by
    intro a ha b hb hab
    apply List.inj_on_of_nodup_map (f := SimpleGraph.Dart.edge)
      (l := w.darts) (by
        simpa [SimpleGraph.Walk.edges] using (canonicalRadiusWitness hω).isPath.isTrail.edges_nodup)
      ha hb
    exact congrArg Subtype.val hab
  have hmap_nodup : (L.map cubicEdgeOfDart).Nodup :=
    (radiusPivotalDarts_nodup hω).map_on fun a ha b hb hab ↦
      hedge_inj a (hLsub a ha) b (hLsub b hb) hab
  have hfinset : (L.map cubicEdgeOfDart).toFinset =
      radiusPivotalEdgeFinset d x n ω := by
    ext e
    constructor
    · intro he
      rw [List.mem_toFinset, List.mem_map] at he
      rcases he with ⟨a, ha, rfl⟩
      rw [radiusPivotalEdgeFinset, Finset.mem_filter]
      have ha' := (mem_radiusPivotalDarts_iff hω a).mp ha
      exact ⟨(canonicalRadiusWitness hω).edge_subset <|
        (mem_walkEdgeFinset_iff _ _).mpr <| by
          rw [SimpleGraph.Walk.edges]
          exact List.mem_map.mpr ⟨a, ha'.1, rfl⟩, ha'.2⟩
    · intro he
      rw [radiusPivotalEdgeFinset, Finset.mem_filter] at he
      have hep := pivotal_mem_witness_walk hω
        (canonicalRadiusWitness hω).sphere_mem (canonicalRadiusWitness hω).walk
        (canonicalRadiusWitness hω).isOpen (canonicalRadiusWitness hω).edge_subset he.2
      rw [SimpleGraph.Walk.edges] at hep
      rcases List.mem_map.mp hep with ⟨a, ha, hae⟩
      rw [List.mem_toFinset, List.mem_map]
      refine ⟨a, ?_, ?_⟩
      · rw [mem_radiusPivotalDarts_iff]
        refine ⟨ha, ?_⟩
        have haee : cubicEdgeOfDart a = e := Subtype.ext hae
        rw [haee]
        exact he.2
      · apply Subtype.ext
        exact hae
  rw [radiusPivotalCount, ← hfinset, List.toFinset_card_of_nodup hmap_nodup,
    List.length_map]

noncomputable def cubicMetricSphereInBall (d : ℕ) (x : Cubic d) (n : ℕ) :
    Finset {y : Cubic d // y ∈ cubicMetricBall d x n} :=
  (cubicMetricBall d x n).attach.filter fun y ↦ y.1 ∈ cubicMetricSphere d x n

@[simp]
theorem mem_cubicMetricSphereInBall {d n : ℕ} {x : Cubic d}
    (y : {q : Cubic d // q ∈ cubicMetricBall d x n}) :
    y ∈ cubicMetricSphereInBall d x n ↔ y.1 ∈ cubicMetricSphere d x n := by
  simp [cubicMetricSphereInBall]

theorem mem_disjointOccurrence_of_edgeDisjoint_openBallWalks {d n : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    {u v : {y : Cubic d // y ∈ cubicMetricBall d x n}}
    (hu : u.1 ∈ cubicMetricSphere d x n) (hv : v.1 ∈ cubicMetricSphere d x n)
    (p : (radiusOpenBallGraph ω).Walk ⟨x, by simp⟩ u)
    (q : (radiusOpenBallGraph ω).Walk ⟨x, by simp⟩ v)
    (hpq : p.edges.Disjoint q.edges) :
    ω ∈ OpenWitnessDisjointOccurrence
      (radiusConnectionEvent d x n) (radiusConnectionEvent d x n) := by
  let p' := p.map (radiusOpenBallToCubicHom ω)
  let q' := q.map (radiusOpenBallToCubicHom ω)
  let H := walkEdgeFinset p'
  let K := walkEdgeFinset q'
  have hHK : Disjoint H K := by
    rw [Finset.disjoint_left]
    intro e heH heK
    have hep : (e : Sym2 (Cubic d)) ∈ p'.edges :=
      (mem_walkEdgeFinset_iff p' e).mp heH
    have heq : (e : Sym2 (Cubic d)) ∈ q'.edges :=
      (mem_walkEdgeFinset_iff q' e).mp heK
    change (e : Sym2 (Cubic d)) ∈
      (p.map (radiusOpenBallToCubicHom ω)).edges at hep
    change (e : Sym2 (Cubic d)) ∈
      (q.map (radiusOpenBallToCubicHom ω)).edges at heq
    rw [SimpleGraph.Walk.edges_map] at hep heq
    obtain ⟨f, hfp, hfe⟩ := List.mem_map.mp hep
    obtain ⟨g, hgq, hge⟩ := List.mem_map.mp heq
    have hfg : f = g := by
      apply Sym2.map.injective Subtype.val_injective
      exact hfe.trans hge.symm
    subst g
    exact List.disjoint_left.mp hpq hfp hgq
  have hHω : (H : Set (CubicEdge d)) ⊆ ω := by
    intro e he
    have he' : (e : Sym2 (Cubic d)) ∈ p'.edges :=
      (mem_walkEdgeFinset_iff p' e).mp he
    exact walkIsOpen_map_radiusOpenBallToCubicHom p e.1 he'
  have hKω : (K : Set (CubicEdge d)) ⊆ ω := by
    intro e he
    have he' : (e : Sym2 (Cubic d)) ∈ q'.edges :=
      (mem_walkEdgeFinset_iff q' e).mp he
    exact walkIsOpen_map_radiusOpenBallToCubicHom q e.1 he'
  have hHA : (H : Set (CubicEdge d)) ∈ radiusConnectionEvent d x n := by
    apply mem_radiusConnectionEvent_iff_exists_connection.mpr
    exact ⟨u.1, hu, p', walkIsOpen_walkEdgeFinset p'⟩
  have hKA : (K : Set (CubicEdge d)) ∈ radiusConnectionEvent d x n := by
    apply mem_radiusConnectionEvent_iff_exists_connection.mpr
    exact ⟨v.1, hv, q', walkIsOpen_walkEdgeFinset q'⟩
  exact ⟨H, K, hHK, hHω, hKω, hHA, hKA⟩

/-- Endpoint case of (5.14): when `r = n-1`, the doubled-terminal target-set Menger theorem
removes the artificial bottleneck at the outer sphere. -/
theorem firstSausageLong_endpoint_mem_disjointOccurrence {d n : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d} (hn : 0 < n)
    (hω : ω ∈ radiusConnectionEvent d x n)
    (hgap : n - 1 < sausageGap d x n ω 1) :
    ω ∈ OpenWitnessDisjointOccurrence
      (radiusConnectionEvent d x n) (radiusConnectionEvent d x n) := by
  classical
  have hnn : n - 1 + 1 ≤ n := by omega
  let y := (canonicalRadiusWitness hω).walk.getVert (firstRadiusHitIndex hω hnn)
  have hydist : cubicL1Dist x y = n := by
    have h := firstRadiusHit_dist_eq hω hnn
    change cubicL1Dist x y = n - 1 + 1 at h
    omega
  have hyball : y ∈ cubicMetricBall d x n := by
    rw [mem_cubicMetricBall_iff_l1Dist_le, hydist]
  let z : {q : Cubic d // q ∈ cubicMetricBall d x n} := ⟨y, hyball⟩
  let q := firstRadiusHitWalk hω hnn
  have hz : z.1 ∈ cubicMetricSphere d x n := by
    rw [mem_cubicMetricSphere_iff_l1Dist_eq]
    exact hydist
  have hqopen : walkIsOpen ω q :=
    walkIsOpen_take (canonicalRadiusWitness hω).walk
      (canonicalRadiusWitness hω).isOpen (firstRadiusHitIndex hω hnn)
  have hWball : ∀ a ∈ (canonicalRadiusWitness hω).walk.support,
      a ∈ cubicMetricBall d x n :=
    walk_support_subset_cubicMetricBall_of_edges (by simp)
      (canonicalRadiusWitness hω).walk (canonicalRadiusWitness hω).edge_subset
  have hqball : ∀ a ∈ q.support, a ∈ cubicMetricBall d x n := by
    intro a ha
    exact hWball a ((SimpleGraph.Walk.isSubwalk_take
      (canonicalRadiusWitness hω).walk (firstRadiusHitIndex hω hnn)).support_subset ha)
  let T := cubicMetricSphereInBall d x n
  have hzT : z ∈ T := by simpa [T] using hz
  let p₀ := (radiusPrefixOpenBallLift z q hqopen hqball).walk
  have havoid : ∀ f : Sym2 {y : Cubic d // y ∈ cubicMetricBall d x n},
      ∃ t ∈ T, ∃ p : (radiusOpenBallGraph ω).Walk ⟨x, by simp⟩ t,
        f ∉ p.edges := by
    intro f
    by_cases hfedge : f ∈ (radiusOpenBallGraph ω).edgeSet
    · let ef : CubicEdge d := ⟨Sym2.map Subtype.val f, by
        induction f using Sym2.inductionOn with
        | _ a b =>
            have hab : (radiusOpenBallGraph ω).Adj a b := by
              rw [← SimpleGraph.mem_edgeSet]
              exact hfedge
            obtain ⟨e, he, _⟩ := hab
            change s(a.1, b.1) ∈ (cubicGraph d).edgeSet
            exact he ▸ e.2⟩
      have hef_nonpiv : ¬IsPivotal (radiusConnectionEvent d x n) ef ω := by
        intro hpiv
        have hefq : (ef : Sym2 (Cubic d)) ∈ q.edges :=
          pivotal_mem_witness_walk hω hz q hqopen
            (walkEdgeFinset_subset_cubicMetricBallEdges_of_support q hqball) hpiv
        have hefFin : ef ∈ walkEdgeFinset q := (mem_walkEdgeFinset_iff q ef).mpr hefq
        exact (firstRadiusHitWalk_edge_not_pivotal_of_lt_sausageGap
          hω hnn hgap hefFin) hpiv
      have hclosed : ω \ {ef} ∈ radiusConnectionEvent d x n :=
        mem_diff_singleton_of_mem_increasingEvent_of_not_pivotal
          (isIncreasingEvent_radiusConnectionEvent d x n) hω hef_nonpiv
      let L := canonicalRadiusOpenBallLiftOfSubset Set.diff_subset hclosed
      let tL : {y : Cubic d // y ∈ cubicMetricBall d x n} :=
        ⟨(canonicalRadiusWitness hclosed).endpoint,
          cubicMetricSphere_subset_ball d x n
            (canonicalRadiusWitness hclosed).sphere_mem⟩
      have ht : tL ∈ T := by
        simpa [T] using (canonicalRadiusWitness hclosed).sphere_mem
      let pL : (radiusOpenBallGraph ω).Walk ⟨x, by simp⟩ tL :=
        L.walk.copy rfl (Subtype.ext rfl)
      refine ⟨tL, ht, pL, ?_⟩
      intro hfL
      have hfL' : f ∈ L.walk.edges := by simpa [pL] using hfL
      have hfW : Sym2.map Subtype.val f ∈ (canonicalRadiusWitness hclosed).walk.edges := by
        rw [← L.map_edges]
        exact List.mem_map.mpr ⟨f, hfL', rfl⟩
      have hefOpen : ef ∈ ω \ {ef} := (canonicalRadiusWitness hclosed).isOpen _ hfW
      exact hefOpen.2 rfl
    · refine ⟨z, hzT, p₀, ?_⟩
      intro hfp
      exact hfedge (p₀.edges_subset_edgeSet hfp)
  obtain ⟨t₁, t₂, p, q, hpq⟩ := TwoEdgeMenger.exists_two_edgeDisjoint_walks_to_finset
    (G := radiusOpenBallGraph ω) hzT p₀ havoid
  apply mem_disjointOccurrence_of_edgeDisjoint_openBallWalks
    ((mem_cubicMetricSphereInBall t₁.1).mp t₁.2)
    ((mem_cubicMetricSphereInBall t₂.1).mp t₂.2) p q hpq

/-- Full deterministic inclusion (5.14), including the endpoint `r = n-1`. -/
theorem firstSausageLong_mem_disjointOccurrence {d n r : ℕ}
    {x : Cubic d} {ω : EdgeConfiguration d}
    (hω : ω ∈ radiusConnectionEvent d x n) (hrn : r + 1 ≤ n)
    (hgap : r < sausageGap d x n ω 1) :
    ω ∈ OpenWitnessDisjointOccurrence
      (radiusConnectionEvent d x (r + 1)) (radiusConnectionEvent d x n) := by
  rcases hrn.lt_or_eq with hlt | heq
  · exact firstSausageLong_mem_disjointOccurrence_of_lt hω hlt hgap
  · have hn : 0 < n := by omega
    have hend := firstSausageLong_endpoint_mem_disjointOccurrence hn hω (by omega)
    simpa [heq] using hend

/-- Full probability form of (5.14), valid for `r+1 ≤ n`. -/
theorem firstSausageLong_probability_le {d n r : ℕ}
    (p : I) (hrn : r + 1 ≤ n) :
    (bernoulliBondMeasure d p).real
        (firstSausageLongEvent d cubicOrigin n r) ≤
      radiusTail d p (r + 1) * radiusTail d p n := by
  calc
    (bernoulliBondMeasure d p).real
        (firstSausageLongEvent d cubicOrigin n r) ≤
        (bernoulliBondMeasure d p).real (OpenWitnessDisjointOccurrence
          (radiusConnectionEvent d cubicOrigin (r + 1))
          (radiusConnectionEvent d cubicOrigin n)) := by
      apply measureReal_mono
      intro ω hω
      exact firstSausageLong_mem_disjointOccurrence hω.1 hrn hω.2
      exact MeasureTheory.measure_ne_top _ _
    _ ≤ (bernoulliBondMeasure d p).real
          (radiusConnectionEvent d cubicOrigin (r + 1)) *
        (bernoulliBondMeasure d p).real
          (radiusConnectionEvent d cubicOrigin n) :=
      bernoulliBondMeasure_real_disjointOccurrence_le_mul p
        (isIncreasingEvent_radiusConnectionEvent d cubicOrigin (r + 1))
        (isIncreasingEvent_radiusConnectionEvent d cubicOrigin n)
        (dependsOn_radiusConnectionEvent d cubicOrigin (r + 1))
        (dependsOn_radiusConnectionEvent d cubicOrigin n)
    _ = radiusTail d p (r + 1) * radiusTail d p n := rfl

/-- Lemma 5.12 for the first sausage, in the unnormalized form equivalent to conditioning on
`A_n`. This formulation avoids division by `P(A_n)`. -/
theorem firstSausageGap_cdf_ge {d n r : ℕ} (p : I) (hrn : r + 1 ≤ n) :
    (1 - radiusTail d p (r + 1)) * radiusTail d p n ≤
      (bernoulliBondMeasure d p).real
        (firstSausageShortEvent d cubicOrigin n r) := by
  let μ := bernoulliBondMeasure d p
  let A := radiusConnectionEvent d cubicOrigin n
  let S := firstSausageShortEvent d cubicOrigin n r
  let L := firstSausageLongEvent d cubicOrigin n r
  have hcover : A ⊆ S ∪ L := by
    intro ω hω
    by_cases h : sausageGap d cubicOrigin n ω 1 ≤ r
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr ⟨hω, lt_of_not_ge h⟩
  have hbase : radiusTail d p n ≤ μ.real (S ∪ L) := by
    simpa [μ, A, radiusTail] using
      measureReal_mono hcover (MeasureTheory.measure_ne_top μ (S ∪ L))
  have hunion : μ.real (S ∪ L) ≤ μ.real S + μ.real L :=
    measureReal_union_le S L
  have hlong : μ.real L ≤ radiusTail d p (r + 1) * radiusTail d p n := by
    simpa [μ, L] using firstSausageLong_probability_le p hrn
  calc
    (1 - radiusTail d p (r + 1)) * radiusTail d p n =
        radiusTail d p n - radiusTail d p (r + 1) * radiusTail d p n := by ring
    _ ≤ μ.real S := by linarith
    _ = (bernoulliBondMeasure d p).real
        (firstSausageShortEvent d cubicOrigin n r) := rfl

end Percolation
