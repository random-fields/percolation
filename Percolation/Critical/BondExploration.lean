import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Percolation.Critical.AdaptiveBernoulliExact
import Percolation.Critical.AdaptiveDecisionOutcome
import Percolation.Critical.FiniteInducedSite

/-!
# Finite boundary-edge exploration

This is the deterministic exploration used in the bond-to-site comparison behind Grimmett's
Theorem 1.33.  The state records the vertices already reached from the root and the undirected
edges already queried.  While the edge boundary is nonempty, the next query is an oriented dart
from the reached set to its complement.  Once that boundary is empty, the exploration issues a
fresh inert query indexed by the history length; this makes the total decision tree well-defined
without ever consuming an edge that could become relevant later.
-/

namespace Percolation

open Classical

namespace FiniteBondExploration

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A query is either an oriented graph edge or an inert post-exhaustion coordinate. -/
abbrev Query := Sum G.Dart ℕ

/-- Directed-edge product coordinates.  Copy `0` is the physical dart used by the bond
exploration; higher copies make repeated malformed site queries genuinely fresh. -/
abbrev DirectedCoordinate := Sum (G.Dart × ℕ) ℕ

/-- Vertices reached from the root and undirected edges whose states have already been read. -/
structure State (V : Type*) where
  reached : Finset V
  queried : Finset (Sym2 V)
deriving DecidableEq

/-- Initial exploration state. -/
def initial (root : V) : State V where
  reached := {root}
  queried := ∅

/-- A real edge query is useful only when its dart currently points out of the reached set.
Every real query is nevertheless recorded.  Inert queries leave the state unchanged. -/
def State.step (s : State V) (q : Query G) (b : Bool) : State V :=
  match q with
  | Sum.inl d =>
      { reached := if b && decide (d.fst ∈ s.reached ∧ d.snd ∉ s.reached) then
          insert d.snd s.reached else s.reached
        queried := insert d.edge s.queried }
  | Sum.inr _ => s

@[simp]
theorem State.step_inr (s : State V) (n : ℕ) (b : Bool) :
    s.step G (Sum.inr n) b = s := by
  rfl

@[simp]
theorem State.step_inl_queried (s : State V) (d : G.Dart) (b : Bool) :
    (s.step G (Sum.inl d) b).queried = insert d.edge s.queried := by
  rfl

theorem State.queried_subset_step (s : State V) (q : Query G) (b : Bool) :
    s.queried ⊆ (s.step G q b).queried := by
  cases q with
  | inl d => simp
  | inr n => simp

theorem State.reached_subset_step (s : State V) (q : Query G) (b : Bool) :
    s.reached ⊆ (s.step G q b).reached := by
  cases q with
  | inr n => simp
  | inl d =>
      simp only [State.step]
      split <;> simp

/-- Replay a chronological query/answer history from an arbitrary state. -/
def stateFrom (s : State V) (history : List (Query G × Bool)) : State V :=
  history.foldl (fun t entry ↦ t.step G entry.1 entry.2) s

/-- Replay from the singleton root state. -/
def stateFromHistory (root : V) (history : List (Query G × Bool)) : State V :=
  stateFrom G (initial root) history

@[simp]
theorem stateFrom_nil (s : State V) : stateFrom G s [] = s := by
  rfl

@[simp]
theorem stateFrom_cons (s : State V) (head : Query G × Bool)
    (tail : List (Query G × Bool)) :
    stateFrom G s (head :: tail) = stateFrom G (s.step G head.1 head.2) tail := by
  rfl

theorem stateFrom_append (s : State V) (left right : List (Query G × Bool)) :
    stateFrom G s (left ++ right) = stateFrom G (stateFrom G s left) right := by
  simp [stateFrom, List.foldl_append]

@[simp]
theorem stateFrom_append_singleton (s : State V) (history : List (Query G × Bool))
    (q : Query G) (b : Bool) :
    stateFrom G s (history ++ [(q, b)]) = (stateFrom G s history).step G q b := by
  rw [stateFrom_append]
  rfl

@[simp]
theorem stateFromHistory_nil (root : V) : stateFromHistory G root [] = initial root := by
  rfl

@[simp]
theorem stateFromHistory_append_singleton (root : V)
    (history : List (Query G × Bool)) (q : Query G) (b : Bool) :
    stateFromHistory G root (history ++ [(q, b)]) =
      (stateFromHistory G root history).step G q b := by
  exact stateFrom_append_singleton G (initial root) history q b

theorem queried_subset_stateFrom (s : State V) (history : List (Query G × Bool)) :
    s.queried ⊆ (stateFrom G s history).queried := by
  induction history generalizing s with
  | nil => simp
  | cons head tail ih =>
      exact (s.queried_subset_step G head.1 head.2).trans
        (ih (s.step G head.1 head.2))

/-- Every real query occurring in a history has its underlying edge recorded in the replayed
state, independently of whether the answer was open or closed. -/
theorem edge_mem_queried_of_mem_history
    (s : State V) (history : List (Query G × Bool)) (d : G.Dart) (b : Bool)
    (hmem : (Sum.inl d, b) ∈ history) :
    d.edge ∈ (stateFrom G s history).queried := by
  induction history generalizing s with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact queried_subset_stateFrom G (s.step G (Sum.inl d) b) tail (by simp)
      · exact ih (s.step G head.1 head.2) htail

/-- Oriented boundary darts whose undirected edges have not yet been queried. -/
def boundaryDarts (s : State V) : Finset G.Dart :=
  Finset.univ.filter fun d ↦
    d.fst ∈ s.reached ∧ d.snd ∉ s.reached ∧ d.edge ∉ s.queried

@[simp]
theorem mem_boundaryDarts_iff (s : State V) (d : G.Dart) :
    d ∈ boundaryDarts G s ↔
      d.fst ∈ s.reached ∧ d.snd ∉ s.reached ∧ d.edge ∉ s.queried := by
  simp [boundaryDarts]

/-- Query the least available boundary dart.  If the boundary is empty, use the fresh inert
coordinate given by the current history length. -/
noncomputable def query (root : V) (history : List (Query G × Bool)) : Query G :=
  let candidates := boundaryDarts G (stateFromHistory G root history)
  if h : candidates.Nonempty then Sum.inl h.choose
  else Sum.inr history.length

theorem query_eq_inl_mem_boundaryDarts (root : V) (history : List (Query G × Bool))
    (d : G.Dart) (hquery : query G root history = Sum.inl d) :
    d ∈ boundaryDarts G (stateFromHistory G root history) := by
  simp only [query] at hquery
  split at hquery
  · rename_i h
    injection hquery with hd
    subst d
    exact h.choose_spec
  · simp at hquery

theorem query_eq_inr_of_boundaryDarts_eq_empty (root : V)
    (history : List (Query G × Bool))
    (hempty : boundaryDarts G (stateFromHistory G root history) = ∅) :
    query G root history = Sum.inr history.length := by
  simp [query, hempty]

theorem query_eq_inr_index (root : V) (history : List (Query G × Bool)) (n : ℕ)
    (hquery : query G root history = Sum.inr n) :
    n = history.length := by
  simp only [query] at hquery
  split at hquery
  · simp at hquery
  · exact Sum.inr.inj hquery.symm

theorem boundaryDarts_eq_empty_of_query_eq_inr
    (root : V) (history : List (Query G × Bool)) (n : ℕ)
    (hquery : query G root history = Sum.inr n) :
    boundaryDarts G (stateFromHistory G root history) = ∅ := by
  simp only [query] at hquery
  split at hquery
  · simp at hquery
  · rename_i h
    exact Finset.not_nonempty_iff_eq_empty.mp h

/-- Inert query indices in a chronological history are strictly smaller than its length. -/
def InertIndicesValid (history : List (Query G × Bool)) : Prop :=
  ∀ n b, (Sum.inr n, b) ∈ history → n < history.length

theorem inertIndicesValid_nil : InertIndicesValid G [] := by
  simp [InertIndicesValid]

theorem InertIndicesValid.append_query (root : V) {history : List (Query G × Bool)}
    (hvalid : InertIndicesValid G history) (b : Bool) :
    InertIndicesValid G
      (history ++ [(query G root history, b)]) := by
  intro n b' hmem
  rw [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hold | hnew
  · have hn := hvalid n b' hold
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · have hquery : query G root history = Sum.inr n := by
      exact congrArg Prod.fst hnew.symm
    have hn := query_eq_inr_index G root history n hquery
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- Generated histories use the length-indexed inert coordinates without repetition. -/
theorem inertIndicesValid_adaptiveQueryHistory (root : V) (bits : List Bool) :
    InertIndicesValid G
      (AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits) := by
  let history := AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits
  induction bits using List.reverseRecOn with
  | nil => exact inertIndicesValid_nil G
  | append_singleton bits b ih =>
      rw [AdaptiveSiteExploration.adaptiveQueryHistory_append_singleton]
      exact InertIndicesValid.append_query G root ih b

/-- Coordinates of the ordinary undirected-edge Bernoulli configuration. -/
def bondCoordinate : Query G → Sum (Sym2 V) ℕ
  | Sum.inl d => Sum.inl d.edge
  | Sum.inr n => Sum.inr n

/-- Coordinates of the independent directed-edge configuration. -/
def dartCoordinate : Query G → DirectedCoordinate G
  | Sum.inl d => Sum.inl (d, 0)
  | Sum.inr n => Sum.inr n

theorem bondCoordinate_inl_injective_on_edge {d e : G.Dart}
    (h : bondCoordinate G (Sum.inl d) = bondCoordinate G (Sum.inl e)) :
    d.edge = e.edge := by
  exact Sum.inl.inj h

theorem dartCoordinate_inl_injective {d e : G.Dart}
    (h : dartCoordinate G (Sum.inl d) = dartCoordinate G (Sum.inl e)) :
    d = e := by
  exact congrArg Prod.fst (Sum.inl.inj h)

/-- The ordinary undirected-edge coordinate selected after a generated history is fresh. -/
theorem bondCoordinate_query_fresh (root : V) (bits : List Bool) :
    let history :=
      AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits
    bondCoordinate G (query G root history) ∉
      AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport
        (bondCoordinate G) history := by
  dsimp only
  let history := AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits
  change bondCoordinate G (query G root history) ∉
    AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport (bondCoordinate G) history
  intro hmem
  unfold AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport at hmem
  obtain ⟨entry, hentry, heq⟩ := Finset.mem_image.mp hmem
  have hentryList : entry ∈ history := by
    simpa using hentry
  rcases entry with ⟨prior, b⟩
  cases hcurrent : query G root history with
  | inl d =>
      have hdBoundary := query_eq_inl_mem_boundaryDarts G root history d hcurrent
      have hdNotQueried := (mem_boundaryDarts_iff G _ _).mp hdBoundary |>.2.2
      cases prior with
      | inl e =>
          have hedge : e.edge = d.edge := by
            have hsum : (Sum.inl e.edge : Sum (Sym2 V) ℕ) = Sum.inl d.edge := by
              simpa [bondCoordinate, hcurrent] using heq
            exact Sum.inl.inj hsum
          apply hdNotQueried
          rw [← hedge]
          exact edge_mem_queried_of_mem_history G (initial root) history e b hentryList
      | inr n => simp [bondCoordinate, hcurrent] at heq
  | inr n =>
      have hn : n = history.length := query_eq_inr_index G root history n hcurrent
      cases prior with
      | inl e => simp [bondCoordinate, hcurrent] at heq
      | inr k =>
          have hk : k = n := by
            have hsum : (Sum.inr k : Sum (Sym2 V) ℕ) = Sum.inr n := by
              simpa [bondCoordinate, hcurrent] using heq
            exact Sum.inr.inj hsum
          have hklt := inertIndicesValid_adaptiveQueryHistory G root bits k b hentryList
          subst k
          rw [hn] at hklt
          exact (Nat.lt_irrefl _ hklt)

/-- The directed-edge coordinate selected after a generated history is fresh. -/
theorem dartCoordinate_query_fresh (root : V) (bits : List Bool) :
    let history :=
      AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits
    dartCoordinate G (query G root history) ∉
      AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport
        (dartCoordinate G) history := by
  dsimp only
  let history := AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits
  change dartCoordinate G (query G root history) ∉
    AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport (dartCoordinate G) history
  intro hmem
  unfold AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport at hmem
  obtain ⟨entry, hentry, heq⟩ := Finset.mem_image.mp hmem
  have hentryList : entry ∈ history := by
    simpa using hentry
  rcases entry with ⟨prior, b⟩
  cases hcurrent : query G root history with
  | inl d =>
      have hdBoundary := query_eq_inl_mem_boundaryDarts G root history d hcurrent
      have hdNotQueried := (mem_boundaryDarts_iff G _ _).mp hdBoundary |>.2.2
      cases prior with
      | inl e =>
          have hedge : e = d := by
            have hsum : (Sum.inl (e, 0) : DirectedCoordinate G) = Sum.inl (d, 0) := by
              simpa [dartCoordinate, hcurrent] using heq
            exact congrArg Prod.fst (Sum.inl.inj hsum)
          apply hdNotQueried
          rw [← hedge]
          exact edge_mem_queried_of_mem_history G (initial root) history e b hentryList
      | inr n => simp [dartCoordinate, hcurrent] at heq
  | inr n =>
      have hn : n = history.length := query_eq_inr_index G root history n hcurrent
      cases prior with
      | inl e => simp [dartCoordinate, hcurrent] at heq
      | inr k =>
          have hk : k = n := by
            have hsum : (Sum.inr k : DirectedCoordinate G) = Sum.inr n := by
              simpa [dartCoordinate, hcurrent] using heq
            exact Sum.inr.inj hsum
          have hklt := inertIndicesValid_adaptiveQueryHistory G root bits k b hentryList
          subst k
          rw [hn] at hklt
          exact (Nat.lt_irrefl _ hklt)

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Exact Bernoulli extension law for the ordinary bond exploration along every generated
history. -/
theorem bondAnswer_exactAlong (p : I) (root : V) :
    ∀ bits : List Bool,
      setBer((Set.univ : Set (Sum (Sym2 V) ℕ)), p).real
          (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
            (AdaptiveSiteExploration.membershipAdaptiveAnswer (bondCoordinate G))
            (AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits ++
              [(query G root
                (AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits), true)])) =
        (p : ℝ) *
          setBer((Set.univ : Set (Sum (Sym2 V) ℕ)), p).real
            (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
              (AdaptiveSiteExploration.membershipAdaptiveAnswer (bondCoordinate G))
              (AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits)) := by
  intro bits
  let admissible : List (Query G × Bool) → Query G → Prop :=
    fun history q ↦ bondCoordinate G q ∉
      AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport (bondCoordinate G) history
  have hexact :=
    AdaptiveSiteExploration.hasAdaptiveAnswerExactOn_membership_of_fresh
      p (bondCoordinate G) admissible (fun _history _q h ↦ h)
  exact hexact _ _ (bondCoordinate_query_fresh G root bits)

/-- Exact Bernoulli extension law for the independent directed-edge exploration along every
generated history. -/
theorem dartAnswer_exactAlong (p : I) (root : V) :
    ∀ bits : List Bool,
      setBer((Set.univ : Set (DirectedCoordinate G)), p).real
          (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
            (AdaptiveSiteExploration.membershipAdaptiveAnswer (dartCoordinate G))
            (AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits ++
              [(query G root
                (AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits), true)])) =
        (p : ℝ) *
          setBer((Set.univ : Set (DirectedCoordinate G)), p).real
            (AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
              (AdaptiveSiteExploration.membershipAdaptiveAnswer (dartCoordinate G))
              (AdaptiveSiteExploration.adaptiveQueryHistory (query G root) bits)) := by
  intro bits
  let admissible : List (Query G × Bool) → Query G → Prop :=
    fun history q ↦ dartCoordinate G q ∉
      AdaptiveSiteExploration.adaptiveHistoryCoordinateSupport (dartCoordinate G) history
  have hexact :=
    AdaptiveSiteExploration.hasAdaptiveAnswerExactOn_membership_of_fresh
      p (dartCoordinate G) admissible (fun _history _q h ↦ h)
  exact hexact _ _ (dartCoordinate_query_fresh G root bits)

/-- Ordinary bonds and independent oriented darts induce the same law on every finite Boolean
decision tree driven by this boundary exploration. -/
theorem bondDecisionWinMass_eq_dartDecisionWinMass
    (p : I) (root : V) (win : List (Query G × Bool) → Prop) (depth : ℕ) :
    AdaptiveSiteExploration.adaptiveDecisionWinMass
        setBer((Set.univ : Set (Sum (Sym2 V) ℕ)), p)
        (AdaptiveSiteExploration.membershipAdaptiveAnswer (bondCoordinate G))
        (query G root) win [] depth =
      AdaptiveSiteExploration.adaptiveDecisionWinMass
        setBer((Set.univ : Set (DirectedCoordinate G)), p)
        (AdaptiveSiteExploration.membershipAdaptiveAnswer (dartCoordinate G))
        (query G root) win [] depth := by
  calc
    _ = ∑ bits : Fin depth → Bool,
        if win (AdaptiveSiteExploration.adaptiveQueryHistory
            (query G root) (List.ofFn bits)) then
          iidBoolWeight depth (p : ℝ) bits else 0 := by
      exact AdaptiveSiteExploration.adaptiveDecisionWinMass_eq_sum_iidBoolWeight_of_exactAlong
        _ (AdaptiveSiteExploration.measurableAnswer_membershipAdaptiveAnswer (bondCoordinate G))
        (query G root) (p : ℝ) (bondAnswer_exactAlong G p root) win depth
    _ = _ := by
      symm
      exact AdaptiveSiteExploration.adaptiveDecisionWinMass_eq_sum_iidBoolWeight_of_exactAlong
        _ (AdaptiveSiteExploration.measurableAnswer_membershipAdaptiveAnswer (dartCoordinate G))
        (query G root) (p : ℝ) (dartAnswer_exactAlong G p root) win depth

/-- The ordinary edge configuration read from the real coordinates of the enlarged product
space. -/
def projectedBondConfiguration (omega : Set (Sum (Sym2 V) ℕ)) : Set (Sym2 V) :=
  {e | Sum.inl e ∈ omega}

/-- Reachability using only edges of an ordinary bond configuration. -/
def BondReachable (root : V) (omega : Set (Sym2 V)) (v : V) : Prop :=
  ∃ w : G.Walk root v, ∀ e ∈ w.edges, e ∈ omega

theorem bondReachable_root (root : V) (omega : Set (Sym2 V)) :
    BondReachable G root omega root := by
  exact ⟨SimpleGraph.Walk.nil, by simp⟩

theorem BondReachable.concat {root x : V} {omega : Set (Sym2 V)}
    (hreach : BondReachable G root omega x) (d : G.Dart)
    (hfst : d.fst = x) (hopen : d.edge ∈ omega) :
    BondReachable G root omega d.snd := by
  subst x
  obtain ⟨w, hw⟩ := hreach
  refine ⟨w.concat d.adj, ?_⟩
  intro e he
  rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
    List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact hw e he
  · exact hopen

/-- Actual Boolean answers produced by reading `coord` through the adaptive boundary query. -/
noncomputable def actualBits {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) (n : ℕ) : Fin n → Bool :=
  AdaptiveSiteExploration.adaptiveDecisionBits
    (AdaptiveSiteExploration.membershipAdaptiveAnswer coord)
    (query G root) omega n

/-- Chronological history produced by the actual coordinate configuration. -/
noncomputable def actualHistory {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) (n : ℕ) :
    List (Query G × Bool) :=
  AdaptiveSiteExploration.adaptiveQueryHistory (query G root)
    (List.ofFn (actualBits G coord omega root n))

/-- Exploration state after the first `n` actual adaptive answers. -/
noncomputable def actualState {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) (n : ℕ) : State V :=
  stateFromHistory G root (actualHistory G coord omega root n)

@[simp]
theorem actualHistory_zero {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) :
    actualHistory G coord omega root 0 = [] := by
  simp [actualHistory, actualBits, AdaptiveSiteExploration.adaptiveQueryHistory]

theorem actualHistory_succ {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) (n : ℕ) :
    actualHistory G coord omega root (n + 1) =
      let history := actualHistory G coord omega root n
      history ++ [(query G root history,
        AdaptiveSiteExploration.membershipAdaptiveAnswer coord omega history
          (query G root history))] := by
  rw [actualHistory, actualHistory, actualBits, actualBits]
  change AdaptiveSiteExploration.adaptiveQueryHistory (query G root)
      (List.ofFn (Fin.snoc
        (AdaptiveSiteExploration.adaptiveDecisionBits
          (AdaptiveSiteExploration.membershipAdaptiveAnswer coord) (query G root) omega n)
        _)) = _
  rw [AdaptiveSiteExploration.adaptiveQueryHistory_ofFn_snoc]

theorem actualState_succ {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) (n : ℕ) :
    actualState G coord omega root (n + 1) =
      let history := actualHistory G coord omega root n
      (actualState G coord omega root n).step G (query G root history)
        (AdaptiveSiteExploration.membershipAdaptiveAnswer coord omega history
          (query G root history)) := by
  rw [actualState, actualState, actualHistory_succ,
    stateFromHistory_append_singleton]

/-- Every vertex discovered by the ordinary-bond exploration is connected to the root by open
ordinary edges. -/
theorem actualState_reached_bondReachable
    (omega : Set (Sum (Sym2 V) ℕ)) (root : V) :
    ∀ n v, v ∈ (actualState G (bondCoordinate G) omega root n).reached →
      BondReachable G root (projectedBondConfiguration omega) v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp [actualState, initial] at hv
      subst v
      exact bondReachable_root G root _
  | succ n ih =>
      intro v hv
      let history := actualHistory G (bondCoordinate G) omega root n
      let s := actualState G (bondCoordinate G) omega root n
      let q := query G root history
      let b := AdaptiveSiteExploration.membershipAdaptiveAnswer (bondCoordinate G)
        omega history q
      rw [actualState_succ] at hv
      change v ∈ (s.step G q b).reached at hv
      cases hq : q with
      | inr k =>
          have hvOld : v ∈ s.reached := by
            simpa [State.step, hq] using hv
          exact ih v (by simpa [s] using hvOld)
      | inl d =>
          have hdBoundary := query_eq_inl_mem_boundaryDarts G root history d (by
            simpa [q] using hq)
          have hdfst : d.fst ∈ s.reached := by
            simpa [s] using (mem_boundaryDarts_iff G _ _).mp hdBoundary |>.1
          have hdsnd : d.snd ∉ s.reached := by
            simpa [s] using (mem_boundaryDarts_iff G _ _).mp hdBoundary |>.2.1
          have hb : b = decide (Sum.inl d.edge ∈ omega) := by
            simp [b, q, hq, AdaptiveSiteExploration.membershipAdaptiveAnswer,
              bondCoordinate]
          by_cases hopen : Sum.inl d.edge ∈ omega
          · have hbtrue : b = true := by simp [hb, hopen]
            have hv' : v ∈ insert d.snd s.reached := by
              simpa [State.step, hq, hbtrue, hdfst, hdsnd] using hv
            rw [Finset.mem_insert] at hv'
            rcases hv' with rfl | hvOld
            · apply BondReachable.concat G
              · exact ih d.fst (by simpa [s] using hdfst)
              · rfl
              · simpa [projectedBondConfiguration] using hopen
            · exact ih v (by simpa [s] using hvOld)
          · have hbfalse : b = false := by simp [hb, hopen]
            have hvOld : v ∈ s.reached := by
              simpa [State.step, hq, hbfalse] using hv
            exact ih v (by simpa [s] using hvOld)

/-- Every queried real coordinate is an edge of `G`. -/
theorem actualState_queried_subset_edgeFinset {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) :
    ∀ n, (actualState G coord omega root n).queried ⊆ G.edgeFinset := by
  intro n
  induction n with
  | zero => simp [actualState, initial]
  | succ n ih =>
      let history := actualHistory G coord omega root n
      let s := actualState G coord omega root n
      let q := query G root history
      let b := AdaptiveSiteExploration.membershipAdaptiveAnswer coord omega history q
      rw [actualState_succ]
      change (s.step G q b).queried ⊆ G.edgeFinset
      cases hq : q with
      | inr k => simpa [State.step, hq, s] using ih
      | inl d =>
          intro e he
          simp only [State.step, hq, State.step_inl_queried, Finset.mem_insert] at he
          rcases he with rfl | heOld
          · exact SimpleGraph.mem_edgeFinset.mpr d.edge_mem
          · exact ih (by simpa [s] using heOld)

/-- Before exhaustion, every step has queried a new edge, so the number of queried edges equals
the elapsed number of steps. -/
theorem boundaryDarts_eq_empty_or_queried_card_eq {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) :
    ∀ n,
      boundaryDarts G (actualState G coord omega root n) = ∅ ∨
        (actualState G coord omega root n).queried.card = n := by
  intro n
  induction n with
  | zero =>
      right
      simp [actualState, initial]
  | succ n ih =>
      let history := actualHistory G coord omega root n
      let s := actualState G coord omega root n
      let q := query G root history
      let b := AdaptiveSiteExploration.membershipAdaptiveAnswer coord omega history q
      rw [actualState_succ]
      change boundaryDarts G (s.step G q b) = ∅ ∨
        (s.step G q b).queried.card = n + 1
      cases hq : q with
      | inr k =>
          left
          have hempty := boundaryDarts_eq_empty_of_query_eq_inr G root history k (by
            simpa [q] using hq)
          simpa [State.step, hq, s] using hempty
      | inl d =>
          right
          have hdBoundary := query_eq_inl_mem_boundaryDarts G root history d (by
            simpa [q] using hq)
          have hdFresh : d.edge ∉ s.queried := by
            simpa [s] using (mem_boundaryDarts_iff G _ _).mp hdBoundary |>.2.2
          have hdS : d ∈ boundaryDarts G s := by
            simpa [s] using hdBoundary
          have hcurrentNonempty : boundaryDarts G s ≠ ∅ := by
            intro hempty
            rw [hempty] at hdS
            simp at hdS
          have hcard : s.queried.card = n := by
            rcases ih with hempty | hcard
            · exact False.elim (hcurrentNonempty (by simpa [s] using hempty))
            · simpa [s] using hcard
          simp [State.step, hq, Finset.card_insert_of_notMem hdFresh, hcard]

/-- A finite graph boundary exploration has exhausted its edge boundary by the number of graph
edges. -/
theorem boundaryDarts_actualState_edgeFinsetCard_eq_empty
    {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) :
    boundaryDarts G
      (actualState G coord omega root G.edgeFinset.card) = ∅ := by
  rcases boundaryDarts_eq_empty_or_queried_card_eq G coord omega root G.edgeFinset.card with
    hempty | hcard
  · exact hempty
  · by_contra hne
    obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hdNot := (mem_boundaryDarts_iff G _ _).mp hd |>.2.2
    have hsubset := actualState_queried_subset_edgeFinset G coord omega root G.edgeFinset.card
    have heq :
        (actualState G coord omega root G.edgeFinset.card).queried = G.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsubset (by rw [hcard])
    apply hdNot
    rw [heq]
    exact SimpleGraph.mem_edgeFinset.mpr d.edge_mem

/-- The root remains reached throughout every actual exploration. -/
theorem root_mem_actualState {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V) :
    ∀ n, root ∈ (actualState G coord omega root n).reached := by
  intro n
  induction n with
  | zero => simp [actualState, initial]
  | succ n ih =>
      rw [actualState_succ]
      exact State.reached_subset_step G _ _ _ ih

/-- Every queried open ordinary edge has both endpoints in the reached set.  This rules out the
subtle failure mode where an edge is consumed before it becomes relevant. -/
theorem queried_open_edge_endpoints_mem_reached
    (omega : Set (Sum (Sym2 V) ℕ)) (root : V) :
    ∀ n (d : G.Dart),
      d.edge ∈ (actualState G (bondCoordinate G) omega root n).queried →
      Sum.inl d.edge ∈ omega →
      d.fst ∈ (actualState G (bondCoordinate G) omega root n).reached ∧
        d.snd ∈ (actualState G (bondCoordinate G) omega root n).reached := by
  intro n
  induction n with
  | zero =>
      intro d hd
      simp [actualState, initial] at hd
  | succ n ih =>
      intro d hdQueried hdOpen
      let history := actualHistory G (bondCoordinate G) omega root n
      let s := actualState G (bondCoordinate G) omega root n
      let q := query G root history
      let b := AdaptiveSiteExploration.membershipAdaptiveAnswer (bondCoordinate G)
        omega history q
      rw [actualState_succ] at hdQueried ⊢
      change d.edge ∈ (s.step G q b).queried at hdQueried
      change d.fst ∈ (s.step G q b).reached ∧ d.snd ∈ (s.step G q b).reached
      cases hq : q with
      | inr k =>
          have hdOld : d.edge ∈ s.queried := by simpa [State.step, hq] using hdQueried
          have hold := ih d (by simpa [s] using hdOld) hdOpen
          simpa [State.step, hq, s] using hold
      | inl e =>
          have heBoundary := query_eq_inl_mem_boundaryDarts G root history e (by
            simpa [q] using hq)
          simp only [hq] at hdQueried ⊢
          have heFst : e.fst ∈ s.reached := by
            simpa [s] using (mem_boundaryDarts_iff G _ _).mp heBoundary |>.1
          have heSnd : e.snd ∉ s.reached := by
            simpa [s] using (mem_boundaryDarts_iff G _ _).mp heBoundary |>.2.1
          have hb : b = decide (Sum.inl e.edge ∈ omega) := by
            simp [b, q, hq, AdaptiveSiteExploration.membershipAdaptiveAnswer,
              bondCoordinate]
          have hdCases : d.edge = e.edge ∨ d.edge ∈ s.queried := by
            simpa [State.step, hq] using hdQueried
          rcases hdCases with hedge | hdOld
          · have heOpen : Sum.inl e.edge ∈ omega := by simpa [hedge] using hdOpen
            have hbtrue : b = true := by simp [hb, heOpen]
            have heFstNew : e.fst ∈ (s.step G (Sum.inl e) b).reached :=
              State.reached_subset_step G s (Sum.inl e) b heFst
            have heSndNew : e.snd ∈ (s.step G (Sum.inl e) b).reached := by
              simp [State.step, hq, hbtrue, heFst, heSnd]
            rcases (SimpleGraph.dart_edge_eq_iff d e).mp hedge with rfl | rfl
            · exact ⟨heFstNew, heSndNew⟩
            · exact ⟨heSndNew, heFstNew⟩
          · have hold := ih d (by simpa [s] using hdOld) hdOpen
            exact ⟨State.reached_subset_step G s (Sum.inl e) b hold.1,
              State.reached_subset_step G s (Sum.inl e) b hold.2⟩

/-- At an exhausted state, an open neighbor of a reached vertex is reached as well. -/
theorem open_neighbor_mem_reached_of_boundaryDarts_eq_empty
    (omega : Set (Sum (Sym2 V) ℕ)) (root x y : V)
    (hxy : G.Adj x y) (hx : x ∈
      (actualState G (bondCoordinate G) omega root G.edgeFinset.card).reached)
    (hopen : Sum.inl s(x, y) ∈ omega)
    (hempty : boundaryDarts G
      (actualState G (bondCoordinate G) omega root G.edgeFinset.card) = ∅) :
    y ∈ (actualState G (bondCoordinate G) omega root G.edgeFinset.card).reached := by
  let d : G.Dart := ⟨(x, y), hxy⟩
  by_contra hy
  have hdNotBoundary : d ∉ boundaryDarts G
      (actualState G (bondCoordinate G) omega root G.edgeFinset.card) := by
    rw [hempty]
    simp
  have hdQueried : d.edge ∈
      (actualState G (bondCoordinate G) omega root G.edgeFinset.card).queried := by
    by_contra hdNotQueried
    have hdNotQueried' : s(x, y) ∉
        (actualState G (bondCoordinate G) omega root G.edgeFinset.card).queried := by
      simpa [d, SimpleGraph.Dart.edge] using hdNotQueried
    apply hdNotBoundary
    simp [d, boundaryDarts, hx, hy, hdNotQueried']
  have hendpoints := queried_open_edge_endpoints_mem_reached G omega root
    G.edgeFinset.card d hdQueried (by simpa [d, SimpleGraph.Dart.edge] using hopen)
  exact hy hendpoints.2

/-- A vertex set closed under traversing the supplied open edges contains the endpoint of every
open walk that starts in the set. -/
theorem walk_end_mem_of_open_edges
    (omega : Set (Sum (Sym2 V) ℕ)) (R : Finset V)
    {u v : V} (w : G.Walk u v) (hu : u ∈ R)
    (hclosed : ∀ x y, G.Adj x y → x ∈ R → Sum.inl s(x, y) ∈ omega → y ∈ R)
    (hw : ∀ e ∈ w.edges, Sum.inl e ∈ omega) :
    v ∈ R := by
  induction w using SimpleGraph.Walk.concatRec with
  | Hnil => exact hu
  | @Hconcat u x y w hxy ih =>
      apply hclosed x y hxy
      · apply ih hu
        intro e he
        apply hw e
        rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
          List.mem_append]
        exact Or.inl he
      · apply hw s(x, y)
        rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
          List.mem_append, List.mem_singleton]
        exact Or.inr rfl

/-- After `|E(G)|` steps, the ordinary exploration has reached every vertex connected to the
root by open bonds. -/
theorem bondReachable_mem_actualState_edgeFinsetCard
    (omega : Set (Sum (Sym2 V) ℕ)) (root v : V)
    (hreach : BondReachable G root (projectedBondConfiguration omega) v) :
    v ∈ (actualState G (bondCoordinate G) omega root G.edgeFinset.card).reached := by
  obtain ⟨w, hw⟩ := hreach
  have hempty := boundaryDarts_actualState_edgeFinsetCard_eq_empty
    G (bondCoordinate G) omega root
  apply walk_end_mem_of_open_edges G omega
    (actualState G (bondCoordinate G) omega root G.edgeFinset.card).reached w
  · exact root_mem_actualState G (bondCoordinate G) omega root _
  · intro x y hxy hx hopen
    exact open_neighbor_mem_reached_of_boundaryDarts_eq_empty
      G omega root x y hxy hx hopen hempty
  · intro e he
    exact hw e he

/-- Green sites generated from independent incoming directed edges, with the root forced green. -/
def directedGreenConfiguration (root : V) (omega : Set (DirectedCoordinate G)) : Set V :=
  {v | v = root ∨ ∃ d : G.Dart, d.snd = v ∧ Sum.inl (d, 0) ∈ omega}

/-- Site reachability through a prescribed green vertex set. -/
def GreenReachable (root : V) (eta : Set V) (v : V) : Prop :=
  ∃ w : G.Walk root v, ∀ z ∈ w.support, z ∈ eta

theorem greenReachable_root (root : V) (eta : Set V) (hroot : root ∈ eta) :
    GreenReachable G root eta root := by
  exact ⟨SimpleGraph.Walk.nil, by simpa⟩

theorem GreenReachable.concat {root x : V} {eta : Set V}
    (hreach : GreenReachable G root eta x) (d : G.Dart)
    (hfst : d.fst = x) (hgreen : d.snd ∈ eta) :
    GreenReachable G root eta d.snd := by
  subst x
  obtain ⟨w, hw⟩ := hreach
  refine ⟨w.concat d.adj, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hw z hz
  · exact hgreen

/-- Every vertex discovered in the directed-edge model is site-connected to the root inside the
incoming-edge green configuration. -/
theorem actualState_reached_greenReachable
    (omega : Set (DirectedCoordinate G)) (root : V) :
    ∀ n v, v ∈ (actualState G (dartCoordinate G) omega root n).reached →
      GreenReachable G root (directedGreenConfiguration G root omega) v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp [actualState, initial] at hv
      subst v
      exact greenReachable_root G root _ (by simp [directedGreenConfiguration])
  | succ n ih =>
      intro v hv
      let history := actualHistory G (dartCoordinate G) omega root n
      let s := actualState G (dartCoordinate G) omega root n
      let q := query G root history
      let b := AdaptiveSiteExploration.membershipAdaptiveAnswer (dartCoordinate G)
        omega history q
      rw [actualState_succ] at hv
      change v ∈ (s.step G q b).reached at hv
      cases hq : q with
      | inr k =>
          have hvOld : v ∈ s.reached := by simpa [State.step, hq] using hv
          exact ih v (by simpa [s] using hvOld)
      | inl d =>
          have hdBoundary := query_eq_inl_mem_boundaryDarts G root history d (by
            simpa [q] using hq)
          have hdfst : d.fst ∈ s.reached := by
            simpa [s] using (mem_boundaryDarts_iff G _ _).mp hdBoundary |>.1
          have hdsnd : d.snd ∉ s.reached := by
            simpa [s] using (mem_boundaryDarts_iff G _ _).mp hdBoundary |>.2.1
          have hb : b = decide (Sum.inl (d, 0) ∈ omega) := by
            simp [b, q, hq, AdaptiveSiteExploration.membershipAdaptiveAnswer,
              dartCoordinate]
          by_cases hopen : Sum.inl (d, 0) ∈ omega
          · have hbtrue : b = true := by simp [hb, hopen]
            have hv' : v ∈ insert d.snd s.reached := by
              simpa [State.step, hq, hbtrue, hdfst, hdsnd] using hv
            rw [Finset.mem_insert] at hv'
            rcases hv' with rfl | hvOld
            · apply GreenReachable.concat G
              · exact ih d.fst (by simpa [s] using hdfst)
              · rfl
              · exact Or.inr ⟨d, rfl, hopen⟩
            · exact ih v (by simpa [s] using hvOld)
          · have hbfalse : b = false := by simp [hb, hopen]
            have hvOld : v ∈ s.reached := by
              simpa [State.step, hq, hbfalse] using hv
            exact ih v (by simpa [s] using hvOld)

/-- Winning predicate used by the bond decision tree. -/
def reachesTarget (root : V) (target : Finset V)
    (history : List (Query G × Bool)) : Prop :=
  ∃ t ∈ target, t ∈ (stateFromHistory G root history).reached

/-- Pointwise semantics of the target-winning decision tree in terms of the actual exploration
state. -/
theorem mem_adaptiveDecisionWinEvent_reachesTarget_iff
    {Iota : Type*} [DecidableEq Iota]
    (coord : Query G → Iota) (omega : Set Iota) (root : V)
    (target : Finset V) (n : ℕ) :
    omega ∈ AdaptiveSiteExploration.adaptiveDecisionWinEvent
        (AdaptiveSiteExploration.membershipAdaptiveAnswer coord)
        (query G root) (reachesTarget G root target) n ↔
      ∃ t ∈ target, t ∈ (actualState G coord omega root n).reached := by
  rw [AdaptiveSiteExploration.mem_adaptiveDecisionWinEvent_iff]
  rfl

/-- Target event for the projected ordinary bond configuration. -/
def projectedBondHitsTargetEvent (root : V) (target : Finset V) :
    Set (Set (Sum (Sym2 V) ℕ)) :=
  {omega | ∃ t ∈ target,
    BondReachable G root (projectedBondConfiguration omega) t}

/-- At the exhaustion depth, the ordinary-bond winning event is exactly the open target
connection event. -/
theorem adaptiveDecisionWinEvent_bond_eq_projectedBondHitsTargetEvent
    (root : V) (target : Finset V) :
    AdaptiveSiteExploration.adaptiveDecisionWinEvent
        (AdaptiveSiteExploration.membershipAdaptiveAnswer (bondCoordinate G))
        (query G root) (reachesTarget G root target) G.edgeFinset.card =
      projectedBondHitsTargetEvent G root target := by
  ext omega
  rw [mem_adaptiveDecisionWinEvent_reachesTarget_iff]
  constructor
  · rintro ⟨t, ht, hreach⟩
    exact ⟨t, ht,
      actualState_reached_bondReachable G omega root G.edgeFinset.card t hreach⟩
  · rintro ⟨t, ht, hreach⟩
    exact ⟨t, ht, bondReachable_mem_actualState_edgeFinsetCard G omega root t hreach⟩

/-- Target event for the incoming-dart green configuration. -/
def directedGreenHitsTargetEvent (root : V) (target : Finset V) :
    Set (Set (DirectedCoordinate G)) :=
  {omega | ∃ t ∈ target,
    GreenReachable G root (directedGreenConfiguration G root omega) t}

/-- Any target reached by the directed-edge exploration is connected through green sites. -/
theorem adaptiveDecisionWinEvent_dart_subset_directedGreenHitsTargetEvent
    (root : V) (target : Finset V) :
    AdaptiveSiteExploration.adaptiveDecisionWinEvent
        (AdaptiveSiteExploration.membershipAdaptiveAnswer (dartCoordinate G))
        (query G root) (reachesTarget G root target) G.edgeFinset.card ⊆
      directedGreenHitsTargetEvent G root target := by
  intro omega hwin
  rw [mem_adaptiveDecisionWinEvent_reachesTarget_iff] at hwin
  obtain ⟨t, ht, hreach⟩ := hwin
  exact ⟨t, ht,
    actualState_reached_greenReachable G omega root G.edgeFinset.card t hreach⟩

/-- The green target event is the preimage of the ordinary site target event under the
incoming-dart green map. -/
theorem directedGreenHitsTargetEvent_eq_preimage_siteHitsFinsetEvent
    (root : V) (target : Finset V) :
    directedGreenHitsTargetEvent G root target =
      (directedGreenConfiguration G root) ⁻¹'
        siteHitsFinsetEvent G root target := by
  rfl

/-- Coupling inequality: ordinary bond target connectivity is bounded by target connectivity in
the incoming-dart green site field. -/
theorem setBernoulli_projectedBondHitsTarget_le_directedGreenHitsTarget
    (p : I) (root : V) (target : Finset V) :
    setBer((Set.univ : Set (Sum (Sym2 V) ℕ)), p).real
        (projectedBondHitsTargetEvent G root target) ≤
      setBer((Set.univ : Set (DirectedCoordinate G)), p).real
        (directedGreenHitsTargetEvent G root target) := by
  rw [← adaptiveDecisionWinEvent_bond_eq_projectedBondHitsTargetEvent]
  rw [AdaptiveSiteExploration.measureReal_adaptiveDecisionWinEvent
    _ (AdaptiveSiteExploration.measurableAnswer_membershipAdaptiveAnswer (bondCoordinate G))]
  rw [bondDecisionWinMass_eq_dartDecisionWinMass G p root
    (reachesTarget G root target) G.edgeFinset.card]
  rw [← AdaptiveSiteExploration.measureReal_adaptiveDecisionWinEvent
    _ (AdaptiveSiteExploration.measurableAnswer_membershipAdaptiveAnswer (dartCoordinate G))]
  exact measureReal_mono
    (adaptiveDecisionWinEvent_dart_subset_directedGreenHitsTargetEvent G root target)

end FiniteBondExploration

end Percolation
