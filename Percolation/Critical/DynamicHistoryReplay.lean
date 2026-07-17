import Percolation.Critical.DynamicLaterSitePartition
import Percolation.Critical.DynamicActiveDirections
import Percolation.Critical.ExplorationHistory

/-!
# Replaying the dynamic block construction from a coarse exploration history

The coarse site oracle is history dependent.  This file gives its literal deterministic replay:
the completed root publishes one outgoing seed per direction; each later accepted site chooses
the earliest accepted neighboring parent, consumes that parent's published seed, runs the
expanded restart schedule of length at most `4d`, and publishes the resulting non-backtracking
half-way-box seeds.
-/

namespace Percolation

open scoped unitInterval

/-- Global finite-history state of the dynamic block construction. -/
structure DynamicBlockHistoryState (d : ℕ) (V : Type*) where
  source : SourceFiniteEdgeRevealState d
  outgoing : V → CubicDirection d → Option (LaterSiteOutgoingSeed d)

namespace DynamicBlockHistoryState

@[ext]
theorem ext {d : ℕ} {V : Type*} {S T : DynamicBlockHistoryState d V}
    (hsource : S.source = T.source) (houtgoing : S.outgoing = T.outgoing) : S = T := by
  cases S
  cases T
  simp_all

/-- Root-completed source state and its literal outgoing seed table. -/
noncomputable def rooted
    {d m n : ℕ} {V : Type*} [DecidableEq V]
    (W : RootRadialSeedProfile d m n) (root : V)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) : DynamicBlockHistoryState d V where
  source := W.rootExtensionPrefixState p radialIncremented incremented id
    (rootExtensionDirectionOrder d).length X
  outgoing := fun v a ↦
    if v = root then W.rootOutgoingSeed p radialIncremented delta incremented X a else none

/-- Every outgoing record currently visible to the coarse exploration names a seed box that
is already contained in the accumulated source exploration. -/
def SeedBoxesInstalled {d m : ℕ} {V : Type*}
    (S : DynamicBlockHistoryState d V) : Prop :=
  ∀ v a U, S.outgoing v a = some U →
    cubicBoxEdges d U.physicalCenter m ⊆ S.source.explored

/-- Completion of all root restarts initializes the global installed-seed invariant. -/
theorem seededBoxesInstalled_rooted
    {d m n : ℕ} {V : Type*} [DecidableEq V] [NeZero d]
    (hm : 1 ≤ m) (hmn : m + 1 < n)
    (W : RootRadialSeedProfile d m n) (root : V)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hadds : W.PolicyAddsOnPrefixes p radialIncremented delta incremented)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length) :
    (rooted W root p radialIncremented delta incremented X).SeedBoxesInstalled
      (m := m) := by
  classical
  intro v a U hU
  by_cases hvr : v = root
  · subst v
    have hseed := W.rootOutgoingSeed_seedBox_subset_completedExplored
      hm hmn p radialIncremented delta incremented X hadds hX a U
        (by simpa [rooted] using hU)
    change cubicBoxEdges d U.physicalCenter m ⊆
      (W.rootExtensionPrefixState p radialIncremented incremented id
        (rootExtensionDirectionOrder d).length X).explored
    rw [RootRadialSeedProfile.rootExtensionPrefixState, List.take_length]
    simpa [RootRadialSeedProfile.completedRootExtensionState] using hseed
  · simp [rooted, hvr] at hU

end DynamicBlockHistoryState

namespace DynamicBlockHistoryReplay

variable {d m n : ℕ} {F : Set (Cubic d)} [LinearOrder F]

/-- Every accepted coarse vertex has already published a literal outgoing record toward each
adjacent vertex that is still undecided in the chronological history.  This invariant is
slightly stronger than frontier coverage and is stable without separately invoking a
frontier-closure lemma. -/
def OutgoingCoversUndecidedNeighbors (history : List (F × Bool))
    (S : DynamicBlockHistoryState d F) : Prop :=
  ∀ u, u ∈ explorationHistoryAccepted history →
    ∀ v, v ∉ explorationHistoryAccepted history →
      v ∉ explorationHistoryRejected history →
      ∀ hAdj : (cubicGraph d).Adj (u : Cubic d) v,
        ∃ U : LaterSiteOutgoingSeed d,
          S.outgoing u (cubicDirectionOfAdjacent hAdj) = some U

/-- A completed root publishes all signed directions, so it covers every initially undecided
neighbor of the root. -/
theorem outgoingCoversUndecidedNeighbors_rooted
    [NeZero d]
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length) :
    OutgoingCoversUndecidedNeighbors [(root, true)]
      (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X) := by
  classical
  intro u hu v _hvAccepted _hvRejected huv
  have hur : u = root := by
    simpa [explorationHistoryAccepted] using hu
  subst u
  let a := cubicDirectionOfAdjacent huv
  obtain ⟨V, hV, _hWitness⟩ := W.exists_rootOutgoingSeedData_of_completion
    p radialIncremented delta incremented X hX a
  refine ⟨⟨cubicRestartFrameIso (W.physicalCenter a) a
      (oppositeTransverseRestartFlip a) V.seedCenter.1, V.seedCenter.1⟩, ?_⟩
  simpa [DynamicBlockHistoryState.rooted, a] using hV

/-- Canonical suffix obtained by replaying only the Boolean decisions through the rooted coarse
exploration.  Arbitrary vertex coordinates supplied in a malformed history are discarded. -/
noncomputable def canonicalSuffix (root : F) (history : List (F × Bool)) :
    List (F × Bool) :=
  ((cubicRegionSiteExploration d F root).replayState history).history.drop 1

/-- Canonical next query reconstructed from a full rooted history.  The full-history encoding is
used by the dynamic runtime so that malformed caller-supplied vertex fields cannot make the
probabilistic oracle and deterministic site replay refer to different coarse vertices. -/
noncomputable def canonicalQueryFromFullHistory (root : F)
    (fullHistory : List (F × Bool)) : F :=
  (cubicRegionSiteExploration d F root).replayQuery root (fullHistory.drop 1)

private theorem siteStep_historyConsistent
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (answer : V → Bool)
    {s : SiteExplorationState V} (hs : s.HistoryConsistent) :
    (E.step answer s).HistoryConsistent := by
  classical
  unfold SiteExplorationState.HistoryConsistent at hs ⊢
  unfold SiteExploration.step
  split
  · exact hs
  next v _hnext =>
    split
    · simp [hs.1, hs.2]
    · simp [hs.1, hs.2]

private theorem replayStateFrom_historyConsistent
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (s : SiteExplorationState V)
    (history : List (V × Bool)) (hs : s.HistoryConsistent) :
    (E.replayStateFrom s history).HistoryConsistent := by
  induction history generalizing s with
  | nil => exact hs
  | cons head history ih =>
      rcases head with ⟨v, accepted⟩
      exact ih (E.step (fun _ ↦ accepted) s)
        (siteStep_historyConsistent E (fun _ ↦ accepted) hs)

private theorem replayStateFrom_wellFormed
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (s : SiteExplorationState V)
    (history : List (V × Bool)) (hs : s.WellFormed) :
    (E.replayStateFrom s history).WellFormed := by
  induction history generalizing s with
  | nil => exact hs
  | cons head history ih =>
      rcases head with ⟨v, accepted⟩
      exact ih (E.step (fun _ ↦ accepted) s)
        (E.step_wellFormed (fun _ ↦ accepted) hs)

private theorem replayStateFrom_openRootedAt
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (root : V) (s : SiteExplorationState V)
    (history : List (V × Bool)) (hs : E.OpenRootedAt root s) :
    E.OpenRootedAt root (E.replayStateFrom s history) := by
  induction history generalizing s with
  | nil => exact hs
  | cons head history ih =>
      rcases head with ⟨v, accepted⟩
      exact ih (E.step (fun _ ↦ accepted) s)
        (E.step_openRootedAt (fun _ ↦ accepted) root hs)

private theorem siteStep_history_head_eq
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (answer : V → Bool)
    (s : SiteExplorationState V) {head : V × Bool}
    (hs : s.history.head? = some head) :
    (E.step answer s).history.head? = some head := by
  classical
  have hsne : s.history ≠ [] := by
    intro hnil
    simp [hnil] at hs
  unfold SiteExploration.step
  split
  · exact hs
  next v _hnext =>
    split
    · rw [List.head?_append_of_ne_nil _ hsne]
      exact hs
    · rw [List.head?_append_of_ne_nil _ hsne]
      exact hs

private theorem replayStateFrom_history_head_eq
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (s : SiteExplorationState V)
    (history : List (V × Bool)) {head : V × Bool}
    (hs : s.history.head? = some head) :
    (E.replayStateFrom s history).history.head? = some head := by
  induction history generalizing s with
  | nil => exact hs
  | cons entry history ih =>
      rcases entry with ⟨v, accepted⟩
      exact ih (E.step (fun _ ↦ accepted) s)
        (siteStep_history_head_eq E (fun _ ↦ accepted) s hs)

theorem cubicRegion_replayState_historyConsistent
    (root : F) (history : List (F × Bool)) :
    ((cubicRegionSiteExploration d F root).replayState history).HistoryConsistent := by
  apply replayStateFrom_historyConsistent
  simp [cubicRegionSiteExploration, rootedSiteExploration,
    SiteExplorationState.HistoryConsistent, explorationHistoryAccepted,
    explorationHistoryRejected]

theorem cubicRegion_replayState_wellFormed
    (root : F) (history : List (F × Bool)) :
    ((cubicRegionSiteExploration d F root).replayState history).WellFormed := by
  apply replayStateFrom_wellFormed
  exact cubicRegionSiteExploration_initial_wellFormed d F root

theorem cubicRegion_replayState_openRootedAt
    (root : F) (history : List (F × Bool)) :
    (cubicRegionSiteExploration d F root).OpenRootedAt root
      ((cubicRegionSiteExploration d F root).replayState history) := by
  apply replayStateFrom_openRootedAt
  exact cubicRegionSiteExploration_initial_openRootedAt d F root

theorem root_cons_canonicalSuffix_eq_replayHistory
    (root : F) (history : List (F × Bool)) :
    [(root, true)] ++ canonicalSuffix root history =
      ((cubicRegionSiteExploration d F root).replayState history).history := by
  let E := cubicRegionSiteExploration d F root
  let s := E.replayState history
  have hhead : s.history.head? = some (root, true) := by
    apply replayStateFrom_history_head_eq
    simp [E, cubicRegionSiteExploration, rootedSiteExploration]
  unfold canonicalSuffix
  change [(root, true)] ++ s.history.drop 1 = s.history
  cases hs : s.history with
  | nil => simp [hs] at hhead
  | cons head tail =>
      rw [hs] at hhead
      have hheadEq : head = (root, true) := by
        exact Option.some.inj hhead
      subst head
      simp

/-- Actual chronological query trace generated from an arbitrary list of Boolean answers.
The vertex fields of the input are ignored, exactly as in `SiteExploration.replayStateFrom`;
when the frontier is exhausted, later Boolean entries generate no trace entry. -/
noncomputable def chronologicalTraceFrom
    {V : Type*} [DecidableEq V] [LinearOrder V] (E : SiteExploration V) :
    SiteExplorationState V → List (V × Bool) → List (V × Bool)
  | _, [] => []
  | s, (_, accepted) :: rest =>
      match SiteExploration.nextVertex s with
      | none => chronologicalTraceFrom E (E.step (fun _ ↦ accepted) s) rest
      | some v => (v, accepted) ::
          chronologicalTraceFrom E (E.step (fun _ ↦ accepted) s) rest

private theorem siteStep_history_eq_of_nextVertex_eq_none
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (answer : V → Bool) (s : SiteExplorationState V)
    (hnext : SiteExploration.nextVertex s = none) :
    (E.step answer s).history = s.history := by
  have hfrontier : s.frontier = ∅ :=
    (SiteExploration.nextVertex_eq_none_iff s).mp hnext
  rw [E.step_eq_self_of_frontier_eq_empty answer hfrontier]

private theorem siteStep_history_eq_append_of_nextVertex_eq_some
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (s : SiteExplorationState V)
    (v : V) (accepted : Bool)
    (hnext : SiteExploration.nextVertex s = some v) :
    (E.step (fun _ ↦ accepted) s).history = s.history ++ [(v, accepted)] := by
  cases accepted <;> simp [SiteExploration.step, hnext]

theorem replayStateFrom_history_eq_append_chronologicalTraceFrom
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (s : SiteExplorationState V)
    (history : List (V × Bool)) :
    (E.replayStateFrom s history).history =
      s.history ++ chronologicalTraceFrom E s history := by
  induction history generalizing s with
  | nil => simp [SiteExploration.replayStateFrom, chronologicalTraceFrom]
  | cons entry history ih =>
      rcases entry with ⟨ignored, accepted⟩
      simp only [SiteExploration.replayStateFrom, chronologicalTraceFrom]
      split
      next hnext =>
        rw [ih, siteStep_history_eq_of_nextVertex_eq_none E _ s hnext]
      next v hnext =>
        rw [ih, siteStep_history_eq_append_of_nextVertex_eq_some E s v accepted hnext,
          List.append_assoc]
        rfl

theorem canonicalSuffix_eq_chronologicalTraceFrom
    (root : F) (history : List (F × Bool)) :
    canonicalSuffix root history =
      chronologicalTraceFrom (cubicRegionSiteExploration d F root)
        (cubicRegionSiteExploration d F root).initial history := by
  rw [canonicalSuffix]
  change ((cubicRegionSiteExploration d F root).replayStateFrom
    (cubicRegionSiteExploration d F root).initial history).history.drop 1 = _
  rw [replayStateFrom_history_eq_append_chronologicalTraceFrom]
  simp [cubicRegionSiteExploration, rootedSiteExploration]

theorem replayStateFrom_chronologicalTraceFrom_eq
    {V : Type*} [DecidableEq V] [LinearOrder V]
    (E : SiteExploration V) (s : SiteExplorationState V)
    (history : List (V × Bool)) :
    E.replayStateFrom s (chronologicalTraceFrom E s history) =
      E.replayStateFrom s history := by
  induction history generalizing s with
  | nil => rfl
  | cons entry history ih =>
      rcases entry with ⟨ignored, accepted⟩
      simp only [chronologicalTraceFrom]
      split
      next hnext =>
        have hfrontier : s.frontier = ∅ :=
          (SiteExploration.nextVertex_eq_none_iff s).mp hnext
        have hstep : E.step (fun _ ↦ accepted) s = s :=
          E.step_eq_self_of_frontier_eq_empty (fun _ ↦ accepted) hfrontier
        simpa [SiteExploration.replayStateFrom, hstep] using
          ih (E.step (fun _ ↦ accepted) s)
      next v hnext =>
        simpa [SiteExploration.replayStateFrom] using
          ih (E.step (fun _ ↦ accepted) s)

theorem replayState_canonicalSuffix_eq
    (root : F) (history : List (F × Bool)) :
    (cubicRegionSiteExploration d F root).replayState (canonicalSuffix root history) =
      (cubicRegionSiteExploration d F root).replayState history := by
  rw [canonicalSuffix_eq_chronologicalTraceFrom]
  exact replayStateFrom_chronologicalTraceFrom_eq
    (cubicRegionSiteExploration d F root)
      (cubicRegionSiteExploration d F root).initial history

theorem canonicalQueryFromFullHistory_root_cons_canonicalSuffix
    (root : F) (history : List (F × Bool)) :
    canonicalQueryFromFullHistory root
        ([(root, true)] ++ canonicalSuffix root history) =
      (cubicRegionSiteExploration d F root).replayQuery root history := by
  unfold canonicalQueryFromFullHistory
  change (cubicRegionSiteExploration d F root).replayQuery root
      (canonicalSuffix root history) =
    (cubicRegionSiteExploration d F root).replayQuery root history
  unfold SiteExploration.replayQuery
  rw [replayState_canonicalSuffix_eq]

/-- Exactly the queries on which the concrete dynamic-block oracle is required to satisfy its
ratio-free lower law: the ambient exploration is active and the supplied vertex is its actual
next query.  Malformed/exhausted histories deliberately impose no probabilistic obligation. -/
def AdmissibleQuery (root : F) (history : List (F × Bool)) (v : F) : Prop :=
  ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty ∧
    v = (cubicRegionSiteExploration d F root).replayQuery root history

theorem canonicalQueryFromFullHistory_eq_of_admissibleQuery
    (root : F) (history : List (F × Bool)) (v : F)
    (hadmissible : AdmissibleQuery root history v) :
    canonicalQueryFromFullHistory root
      ([(root, true)] ++ canonicalSuffix root history) = v := by
  rw [canonicalQueryFromFullHistory_root_cons_canonicalSuffix]
  exact hadmissible.2.symm

/-- On an active replay, appending one Boolean answer appends the deterministic next query to
the canonical chronological suffix.  The caller-supplied vertex is used only through the
admissibility equality, so this remains robust against malformed inactive histories. -/
theorem canonicalSuffix_append_singleton_of_admissibleQuery
    (root : F) (history : List (F × Bool)) (v : F) (accepted : Bool)
    (hadmissible : AdmissibleQuery root history v) :
    canonicalSuffix root (history ++ [(v, accepted)]) =
      canonicalSuffix root history ++ [(v, accepted)] := by
  let E := cubicRegionSiteExploration d F root
  let s := E.replayState history
  have hnext : SiteExploration.nextVertex s = some v := by
    have hquery : E.replayQuery root history = v := hadmissible.2.symm
    have hfrontier : s.frontier.Nonempty := by
      simpa [s, E] using hadmissible.1
    have hnextQuery : SiteExploration.nextVertex s =
        some (E.replayQuery root history) := by
      simp [SiteExploration.nextVertex, SiteExploration.replayQuery, hfrontier, s]
    simpa [hquery] using hnextQuery
  have hstepHistory : (E.step (fun _ ↦ accepted) s).history =
      s.history ++ [(v, accepted)] :=
    siteStep_history_eq_append_of_nextVertex_eq_some E s v accepted hnext
  have hcanonical :
      [(root, true)] ++ canonicalSuffix root (history ++ [(v, accepted)]) =
        ([(root, true)] ++ canonicalSuffix root history) ++ [(v, accepted)] := by
    calc
      [(root, true)] ++ canonicalSuffix root (history ++ [(v, accepted)]) =
          (E.replayState (history ++ [(v, accepted)])).history := by
        simpa [E] using root_cons_canonicalSuffix_eq_replayHistory
          (d := d) root (history ++ [(v, accepted)])
      _ = (E.step (fun _ ↦ accepted) s).history := by
        rw [E.replayState_append_singleton]
      _ = s.history ++ [(v, accepted)] := hstepHistory
      _ = ([(root, true)] ++ canonicalSuffix root history) ++ [(v, accepted)] := by
        rw [root_cons_canonicalSuffix_eq_replayHistory]
  have hdrop := congrArg (List.drop 1) hcanonical
  simpa using hdrop

theorem admissibleQuery_replayQuery (root : F) (history : List (F × Bool))
    (hfrontier :
      ((cubicRegionSiteExploration d F root).replayState history).frontier.Nonempty) :
    AdmissibleQuery root history
      ((cubicRegionSiteExploration d F root).replayQuery root history) :=
  ⟨hfrontier, rfl⟩

/-- Total parent choice.  On a genuine frontier history the first branch is taken and agrees
with `historyInletParent`; malformed histories fall back to the root. -/
noncomputable def inletParent (root : F) (history : List (F × Bool)) (v : F) : F :=
  let E := AdaptiveSiteExploration.cubicRegion d F root
  if h : (E.historyInletCandidates history v).Nonempty then
    E.historyInletParent history v h
  else root

/-- Total incoming signed direction.  Genuine frontier histories use their ambient cubic
adjacency; malformed histories use the positive first coordinate. -/
noncomputable def incomingDirection (hd : 0 < d) (root : F)
    (history : List (F × Bool)) (v : F) : CubicDirection d :=
  by
    classical
    let u := inletParent root history v
    exact if h : (cubicGraph d).Adj (u : Cubic d) v then cubicDirectionOfAdjacent h
      else (⟨0, hd⟩, true)

/-- Seed record offered by the chosen parent, totalized only on malformed/failed histories. -/
noncomputable def inletSeed (hd : 0 < d) (root : F)
    (history : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F) : LaterSiteOutgoingSeed d :=
  let u := inletParent root history v
  let a := incomingDirection hd root history v
  (S.outgoing u a).getD ⟨cubicOrigin, cubicOrigin⟩

/-- Once the chosen parent table is populated, the totalized inlet selector returns that
literal record and its physical seed box is certified by the global history-state invariant. -/
theorem inletSeed_eq_and_seedBox_subset_of_outgoing_eq_some
    (hd : 0 < d) (root : F) (history : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F) (U : LaterSiteOutgoingSeed d)
    (hinstalled : S.SeedBoxesInstalled (m := m))
    (hU : S.outgoing (inletParent root history v)
      (incomingDirection hd root history v) = some U) :
    inletSeed hd root history v S = U ∧
      cubicBoxEdges d U.physicalCenter m ⊆ S.source.explored := by
  constructor
  · simp [inletSeed, hU]
  · exact hinstalled _ _ U hU

/-- On an admissible coarse query the totalized inlet selector never takes its dummy branch:
the canonical parent is accepted, its outgoing table contains the required signed direction,
and the selected physical seed box is already installed in the global explored state. -/
theorem exists_inletSeed_eq_and_seedBox_subset_of_admissibleQuery
    (hd : 0 < d) (root : F) (history : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F)
    (hadmissible : AdmissibleQuery root history v)
    (hcover : OutgoingCoversUndecidedNeighbors
      ([(root, true)] ++ canonicalSuffix root history) S)
    (hinstalled : S.SeedBoxesInstalled (m := m)) :
    ∃ U : LaterSiteOutgoingSeed d,
      inletSeed hd root ([(root, true)] ++ canonicalSuffix root history) v S = U ∧
        cubicBoxEdges d U.physicalCenter m ⊆ S.source.explored ∧
        S.outgoing
          (inletParent root ([(root, true)] ++ canonicalSuffix root history) v)
          (incomingDirection hd root ([(root, true)] ++ canonicalSuffix root history) v) =
            some U := by
  classical
  let E := cubicRegionSiteExploration d F root
  let s := E.replayState history
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  have hfull : fullHistory = s.history := by
    simpa [fullHistory, s, E] using
      root_cons_canonicalSuffix_eq_replayHistory (d := d) root history
  have hfrontier : s.frontier.Nonempty := by
    simpa [AdmissibleQuery, s, E] using hadmissible.1
  have hnext : SiteExploration.nextVertex s = some (E.replayQuery root history) := by
    simp [SiteExploration.nextVertex, SiteExploration.replayQuery, hfrontier, s]
  have hvQuery : v = E.replayQuery root history := by
    simpa [E] using hadmissible.2
  have hvfrontier : v ∈ s.frontier := by
    apply SiteExploration.mem_frontier_of_nextVertex_eq_some
    simpa [hvQuery] using hnext
  have hwell : s.WellFormed := by
    simpa [s, E] using cubicRegion_replayState_wellFormed (d := d) root history
  have hconsistent : s.HistoryConsistent := by
    simpa [s, E] using cubicRegion_replayState_historyConsistent (d := d) root history
  have hopen : E.OpenRootedAt root s := by
    simpa [s, E] using cubicRegion_replayState_openRootedAt (d := d) root history
  have hvNotDecided : v ∉ s.decided := by
    exact Finset.disjoint_left.mp hwell.2 hvfrontier
  have hvNotOccupied : v ∉ s.occupied := fun hv ↦
    hvNotDecided (Finset.mem_union_left _ hv)
  have hvNotRejected : v ∉ s.rejected := fun hv ↦
    hvNotDecided (Finset.mem_union_right _ hv)
  have hvNotAcceptedHistory : v ∉ explorationHistoryAccepted fullHistory := by
    rw [hfull, ← hconsistent.1]
    exact hvNotOccupied
  have hvNotRejectedHistory : v ∉ explorationHistoryRejected fullHistory := by
    rw [hfull, ← hconsistent.2]
    exact hvNotRejected
  obtain ⟨u, huOccupied, huvInduced⟩ := hopen.2.2 v hvfrontier
  have huAcceptedHistory : u ∈ explorationHistoryAccepted fullHistory := by
    rw [hfull, ← hconsistent.1]
    exact huOccupied
  let EA := AdaptiveSiteExploration.cubicRegion d F root
  have hne : (EA.historyInletCandidates fullHistory v).Nonempty := by
    refine ⟨u, ?_⟩
    rw [AdaptiveSiteExploration.historyInletCandidates, Finset.mem_filter]
    refine ⟨huAcceptedHistory, ?_⟩
    simpa [EA, E, AdaptiveSiteExploration.cubicRegion, SiteExploration.toAdaptive] using
      huvInduced
  let parent := EA.historyInletParent fullHistory v hne
  have hparentAccepted : parent ∈ explorationHistoryAccepted fullHistory :=
    EA.historyInletParent_mem_accepted fullHistory v hne
  have hparentAdjInduced : EA.graph.Adj parent v :=
    EA.historyInletParent_adj fullHistory v hne
  have hparentAdj : (cubicGraph d).Adj (parent : Cubic d) v := by
    exact SimpleGraph.induce_adj.mp hparentAdjInduced
  have hparent : inletParent root fullHistory v = parent := by
    simp [inletParent, EA, hne, parent]
  have hincoming : incomingDirection hd root fullHistory v =
      cubicDirectionOfAdjacent hparentAdj := by
    simp [incomingDirection, hparent, hparentAdj]
  obtain ⟨U, hU⟩ := hcover parent hparentAccepted v hvNotAcceptedHistory
    hvNotRejectedHistory hparentAdj
  have hU' : S.outgoing (inletParent root fullHistory v)
      (incomingDirection hd root fullHistory v) = some U := by
    simpa [hparent, hincoming] using hU
  refine ⟨U, ?_, ?_, ?_⟩
  · exact (inletSeed_eq_and_seedBox_subset_of_outgoing_eq_some
      (m := m) hd root fullHistory v S U hinstalled hU').1
  · exact (inletSeed_eq_and_seedBox_subset_of_outgoing_eq_some
      (m := m) hd root fullHistory v S U hinstalled hU').2
  · simpa [fullHistory] using hU'

theorem inletSeed_seedBox_subset_of_admissibleQuery
    (hd : 0 < d) (root : F) (history : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F)
    (hadmissible : AdmissibleQuery root history v)
    (hcover : OutgoingCoversUndecidedNeighbors
      ([(root, true)] ++ canonicalSuffix root history) S)
    (hinstalled : S.SeedBoxesInstalled (m := m)) :
    cubicBoxEdges d
      (inletSeed hd root ([(root, true)] ++ canonicalSuffix root history) v S
        ).physicalCenter m ⊆ S.source.explored := by
  obtain ⟨U, hseed, hU, _hOutgoing⟩ :=
    exists_inletSeed_eq_and_seedBox_subset_of_admissibleQuery
      (m := m) hd root history v S hadmissible hcover hinstalled
  rw [hseed]
  exact hU

/-- On a genuine query, the total inlet selector is the literal outgoing record published by
its accepted parent.  This form is used to invoke the final-density replay connection theorem
for the anchor selected at the query's acceptance time. -/
theorem inletSeed_parent_outgoing_of_admissibleQuery
    (hd : 0 < d) (root : F) (history : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F)
    (hadmissible : AdmissibleQuery root history v)
    (hcover : OutgoingCoversUndecidedNeighbors
      ([(root, true)] ++ canonicalSuffix root history) S)
    (hinstalled : S.SeedBoxesInstalled (m := m)) :
    S.outgoing
        (inletParent root ([(root, true)] ++ canonicalSuffix root history) v)
        (incomingDirection hd root ([(root, true)] ++ canonicalSuffix root history) v) =
      some (inletSeed hd root ([(root, true)] ++ canonicalSuffix root history) v S) := by
  obtain ⟨U, hseed, _hbox, hU⟩ :=
    exists_inletSeed_eq_and_seedBox_subset_of_admissibleQuery
      (m := m) hd root history v S hadmissible hcover hinstalled
  rw [hseed]
  exact hU

/-- First inlet steering mask computed from the parent's published reference displacement. -/
noncomputable def firstFlip (hd : 0 < d) (root : F)
    (history : List (F × Bool)) (v : F)
    (S : DynamicBlockHistoryState d F) : Fin d → Bool :=
  inletCompensatingTransverseFlip (incomingDirection hd root history v)
    (inletSeed hd root history v S).referenceCenter

/-- The old explicit second-mask parameter is ignored by the runtime: slot two reads the first
selected reference center stored in `LaterSiteRuntime.firstReferenceTarget`. -/
def unusedSecondFlip : Fin d → Bool := fun _ ↦ false

/-- Source-faithful schedule for the queried site.  The first two entries carry the inlet seed
into the new block.  Later entries are precisely the non-parent directions whose coarse
endpoint has not already been accepted or rejected through another route. -/
noncomputable def siteDirectionOrder (hd : 0 < d) (root : F)
    (history : List (F × Bool)) (v : F) : List (CubicDirection d) :=
  activeLaterSiteDirectionOrder history v (incomingDirection hd root history v)

theorem siteDirectionOrder_length_le (hd : 0 < d) (root : F)
    (history : List (F × Bool)) (v : F) :
    (siteDirectionOrder hd root history v).length ≤ 4 * d := by
  exact activeLaterSiteDirectionOrder_length_le hd history v
    (incomingDirection hd root history v)

/-- Total runtime used to decide one queried coarse site. -/
noncomputable def siteRuntime (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F) : LaterSiteRuntime d :=
  let seed := inletSeed hd root history v S
  LaterSiteRuntime.runFrom hmn seed.physicalCenter
    (incomingDirection hd root history v) (firstFlip hd root history v S)
    unusedSecondFlip p delta incremented X
      (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
      (siteDirectionOrder hd root history v)

/-- Every active fresh branch of the source-faithful runtime publishes a final outgoing seed.
The published entry is the result of the second application in that branch's adjacent pair, so
it is the half-way-box anchor rather than the provisional face seed. -/
theorem exists_siteRuntime_outgoing_of_active
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (a : CubicDirection d)
    (ha : a ∈ activeLaterSiteBranchDirections F history v
      (incomingDirection hd root history v)) :
    ∃ U : LaterSiteOutgoingSeed d,
      (siteRuntime hd hmn root history v p delta incremented X S).outgoing a = some U := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let branches :=
    (activeLaterSiteBranchDirections F history v incoming).toList
  let R0 := LaterSiteRuntime.initial S.source seed.physicalCenter
  let R2 := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
    p delta incremented X R0 0 [incoming, incoming]
  have haList : a ∈ branches := by
    simpa [branches, incoming] using ha
  have hpair := LaterSiteRuntime.exists_outgoing_runFrom_branchPairs hmn
    seed.physicalCenter incoming first unusedSecondFlip p delta incremented X R2 2
      branches (by exact Finset.nodup_toList _) a haList (by omega)
  have hdirections :
      siteDirectionOrder hd root history v =
        [incoming, incoming] ++ branches.flatMap laterSiteBranchRestartPair := by
    simp [siteDirectionOrder, activeLaterSiteDirectionOrder, incoming, branches]
  change ∃ U : LaterSiteOutgoingSeed d,
    (LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
      p delta incremented X R0 0 (siteDirectionOrder hd root history v)).outgoing a = some U
  rw [hdirections, LaterSiteRuntime.runFrom_append]
  simpa [R2] using hpair

/-- One replayed coarse decision.  Failed sites retain no outgoing table; accepted sites publish
the branch table computed by their completed runtime. -/
noncomputable def step (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F) :
    DynamicBlockHistoryState d F :=
  let R := siteRuntime hd hmn root history v p delta incremented X S
  { source := R.source
    outgoing := if accepted then Function.update S.outgoing v R.outgoing else S.outgoing }

/-- A rejected coarse site does not publish new seeds, while its total source replay only
enlarges the explored set; hence all previously published seed certificates survive. -/
theorem seededBoxesInstalled_step_false
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hS : S.SeedBoxesInstalled (m := m)) :
    (step hd hmn root history v false p delta incremented X S
      ).SeedBoxesInstalled (m := m) := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  let R0 := LaterSiteRuntime.initial S.source seed.physicalCenter
  have hmono := LaterSiteRuntime.source_explored_subset_runFrom hmn seed.physicalCenter
    incoming first unusedSecondFlip p delta incremented X R0 0 directions
  intro u a U hU
  have hUold : S.outgoing u a = some U := by
    simpa [step, siteRuntime, seed, incoming, first, directions, R0] using hU
  exact fun e he ↦ hmono (hS u a U hUold he)

/-- A successful accepted coarse site preserves all old seed boxes and installs every new
outgoing record published by its completed runtime. -/
theorem seededBoxesInstalled_step_true_of_success
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hS : S.SeedBoxesInstalled (m := m))
    (hinlet : cubicBoxEdges d
      (inletSeed hd root history v S).physicalCenter m ⊆ S.source.explored)
    (hsuccess :
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let directions := siteDirectionOrder hd root history v
      LaterSiteRuntime.succeedsFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 directions)
    (hready :
      let seed := inletSeed hd root history v S
      let incoming := incomingDirection hd root history v
      let first := firstFlip hd root history v S
      let directions := siteDirectionOrder hd root history v
      ∀ j (hj : j < directions.length),
        let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
          unusedSecondFlip p delta incremented X
            (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 (directions.take j)
        let a := directions[j]
        Disjoint
            (cubicEdgeEndpointVertices (Rj.source.referenceExploredEdges
              (cubicRestartFrameIso (Rj.slotCenterFor seed.physicalCenter a j) a
                (Rj.slotTransverseFlip incoming first unusedSecondFlip a j))))
            (cubicEdgeEndpointVertices (seededBoundaryTargetSupport d a.1 m n)) ∧
          ∀ e ∈ (Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
            ).boundarySupport n,
            ((Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip a j
              ).physicalBoundaryThreshold e : ℝ) + delta ≤
              (incremented Rj.source a e : ℝ)) :
    (step hd hmn root history v true p delta incremented X S
      ).SeedBoxesInstalled (m := m) := by
  let seed := inletSeed hd root history v S
  let incoming := incomingDirection hd root history v
  let first := firstFlip hd root history v S
  let directions := siteDirectionOrder hd root history v
  let R0 := LaterSiteRuntime.initial S.source seed.physicalCenter
  let R := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first unusedSecondFlip
    p delta incremented X R0 0 directions
  have hR0 : R0.SeedBoxesInstalled m := by
    exact LaterSiteRuntime.seedBoxesInstalled_initial S.source seed.physicalCenter hinlet
  have hR : R.SeedBoxesInstalled m := by
    apply LaterSiteRuntime.seedBoxesInstalled_runFrom_of_succeedsFrom
      seed.physicalCenter incoming first unusedSecondFlip p delta incremented X R0 0
        directions hR0
    · simpa [seed, incoming, first, directions, R0] using hsuccess
    · simpa [seed, incoming, first, directions, R0] using hready
  intro u a U hU
  by_cases huv : u = v
  · subst u
    have hUR : R.outgoing a = some U := by
      simpa [step, siteRuntime, seed, incoming, first, directions, R0, R] using hU
    simpa [step, siteRuntime, seed, incoming, first, directions, R0, R] using
      hR.2.2 a U hUR
  · have hUold : S.outgoing u a = some U := by
      simpa [step, siteRuntime, seed, incoming, first, directions, R0, R, huv] using hU
    have hmono := LaterSiteRuntime.source_explored_subset_runFrom hmn seed.physicalCenter
      incoming first unusedSecondFlip p delta incremented X R0 0 directions
    simpa [step, siteRuntime, seed, incoming, first, directions, R0, R] using
      (fun e he ↦ hmono (hS u a U hUold he))

/-- The outgoing-table coverage invariant is preserved by one genuine chronological coarse
decision.  On acceptance the new site publishes exactly the active non-backtracking branches;
the only excluded direction points to its already accepted inlet parent. -/
theorem outgoingCoversUndecidedNeighbors_step
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (history : List (F × Bool)) (v : F) (accepted : Bool)
    (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (S : DynamicBlockHistoryState d F)
    (hcover : OutgoingCoversUndecidedNeighbors history S)
    (hvAccepted : v ∉ explorationHistoryAccepted history)
    (hvRejected : v ∉ explorationHistoryRejected history)
    (hne : ((AdaptiveSiteExploration.cubicRegion d F root
      ).historyInletCandidates history v).Nonempty) :
    OutgoingCoversUndecidedNeighbors (history ++ [(v, accepted)])
      (step hd hmn root history v accepted p delta incremented X S) := by
  classical
  let E := AdaptiveSiteExploration.cubicRegion d F root
  let parent := E.historyInletParent history v hne
  have hparentAccepted : parent ∈ explorationHistoryAccepted history :=
    E.historyInletParent_mem_accepted history v hne
  have hparentAdjInduced : E.graph.Adj parent v :=
    E.historyInletParent_adj history v hne
  have hparentAdj : (cubicGraph d).Adj (parent : Cubic d) v := by
    exact SimpleGraph.induce_adj.mp hparentAdjInduced
  have hparentEq : inletParent root history v = parent := by
    simp [inletParent, parent, E, hne]
  have hincoming : incomingDirection hd root history v =
      cubicDirectionOfAdjacent hparentAdj := by
    rw [incomingDirection]
    rw [hparentEq, dif_pos hparentAdj]
  cases accepted
  · intro u hu w hwAccepted hwRejected huw
    have huOld : u ∈ explorationHistoryAccepted history := by
      simpa using hu
    have hwAcceptedOld : w ∉ explorationHistoryAccepted history := by
      simpa using hwAccepted
    have hwRejectedOld : w ∉ explorationHistoryRejected history := by
      have hpair : w ≠ v ∧ w ∉ explorationHistoryRejected history := by
        simpa only [explorationHistoryRejected_append_false, Finset.mem_insert,
          not_or] using hwRejected
      exact hpair.2
    obtain ⟨U, hU⟩ := hcover u huOld w hwAcceptedOld hwRejectedOld huw
    exact ⟨U, by simpa [step] using hU⟩
  · intro u hu w hwAccepted hwRejected huw
    have huCases : u = v ∨ u ∈ explorationHistoryAccepted history := by
      simpa only [explorationHistoryAccepted_append_true, Finset.mem_insert] using hu
    have hwAcceptedOld : w ∉ explorationHistoryAccepted history := by
      have hpair : w ≠ v ∧ w ∉ explorationHistoryAccepted history := by
        simpa only [explorationHistoryAccepted_append_true, Finset.mem_insert,
          not_or] using hwAccepted
      exact hpair.2
    have hwRejectedOld : w ∉ explorationHistoryRejected history := by
      simpa only [explorationHistoryRejected_append_true] using hwRejected
    rcases huCases with huEq | huOld
    · subst u
      let a := cubicDirectionOfAdjacent huw
      let incoming := incomingDirection hd root history v
      have haStep : cubicStepFrom (v : Cubic d) a = (w : Cubic d) := by
        exact cubicStepFrom_directionOfAdjacent huw
      have hparentStep : cubicStepFrom (v : Cubic d)
          (reverseCubicDirection incoming) = (parent : Cubic d) := by
        dsimp [incoming]
        rw [hincoming]
        calc
          cubicStepFrom (v : Cubic d)
              (reverseCubicDirection (cubicDirectionOfAdjacent hparentAdj)) =
            cubicStepFrom
              (cubicStepFrom (parent : Cubic d) (cubicDirectionOfAdjacent hparentAdj))
              (reverseCubicDirection (cubicDirectionOfAdjacent hparentAdj)) := by
                congr 1
                exact (cubicStepFrom_directionOfAdjacent hparentAdj).symm
          _ = (parent : Cubic d) := cubicStepFrom_reverse (parent : Cubic d)
            (cubicDirectionOfAdjacent hparentAdj)
      have hback : a ≠ reverseCubicDirection incoming := by
        intro ha
        have hwp : w = parent := by
          apply Subtype.ext
          exact haStep.symm.trans ((congrArg (cubicStepFrom (v : Cubic d)) ha).trans
            hparentStep)
        subst w
        exact hwAcceptedOld hparentAccepted
      have haActive : a ∈ activeLaterSiteBranchDirections F history v incoming := by
        rw [mem_activeLaterSiteBranchDirections_iff]
        refine ⟨hback, w, haStep, ?_⟩
        rw [mem_explorationHistoryDecided_iff]
        exact not_or_intro hwAcceptedOld hwRejectedOld
      obtain ⟨U, hU⟩ := exists_siteRuntime_outgoing_of_active hd hmn root history v
        p delta incremented X S a (by simpa [incoming] using haActive)
      refine ⟨U, ?_⟩
      simpa [step, a] using hU
    · have huv : u ≠ v := by
        intro huv
        subst u
        exact hvAccepted huOld
      obtain ⟨U, hU⟩ := hcover u huOld w hwAcceptedOld hwRejectedOld huw
      refine ⟨U, ?_⟩
      simpa [step, huv] using hU

/-- Replay a suffix while retaining the full preceding coarse history used for inlet choices. -/
noncomputable def replayFrom (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) :
    List (F × Bool) → DynamicBlockHistoryState d F → List (F × Bool) →
      DynamicBlockHistoryState d F
  | _, S, [] => S
  | prior, S, (v, accepted) :: rest =>
      replayFrom hd hmn root p delta incremented X (prior ++ [(v, accepted)])
        (step hd hmn root prior v accepted p delta incremented X S) rest

/-- The outgoing-table invariant follows the actual chronological trace generated by the site
exploration.  This induction is deliberately driven by the site state rather than by the
untrusted vertex fields of the caller-supplied history. -/
private theorem outgoingCoversUndecidedNeighbors_replayFrom_chronologicalTrace
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ)
    (s : SiteExplorationState F) (S : DynamicBlockHistoryState d F)
    (history : List (F × Bool))
    (hwell : s.WellFormed) (hconsistent : s.HistoryConsistent)
    (hopen : (cubicRegionSiteExploration d F root).OpenRootedAt root s)
    (hcover : OutgoingCoversUndecidedNeighbors s.history S) :
    OutgoingCoversUndecidedNeighbors
      (((cubicRegionSiteExploration d F root).replayStateFrom s history).history)
      (replayFrom hd hmn root p delta incremented X s.history S
        (chronologicalTraceFrom (cubicRegionSiteExploration d F root) s history)) := by
  classical
  let E := cubicRegionSiteExploration d F root
  induction history generalizing s S with
  | nil => simpa [E, SiteExploration.replayStateFrom, chronologicalTraceFrom, replayFrom]
      using hcover
  | cons entry history ih =>
      rcases entry with ⟨ignored, accepted⟩
      simp only [chronologicalTraceFrom]
      split
      next hnext =>
        have hfrontier : s.frontier = ∅ :=
          (SiteExploration.nextVertex_eq_none_iff s).mp hnext
        have hstep : E.step (fun _ ↦ accepted) s = s :=
          E.step_eq_self_of_frontier_eq_empty (fun _ ↦ accepted) hfrontier
        have hih := ih (E.step (fun _ ↦ accepted) s) S
          (E.step_wellFormed (fun _ ↦ accepted) hwell)
          (siteStep_historyConsistent E (fun _ ↦ accepted) hconsistent)
          (E.step_openRootedAt (fun _ ↦ accepted) root hopen)
          (by simpa [hstep] using hcover)
        simpa [E, SiteExploration.replayStateFrom, hstep] using hih
      next v hnext =>
        have hvfrontier : v ∈ s.frontier :=
          SiteExploration.mem_frontier_of_nextVertex_eq_some hnext
        have hvNotDecided : v ∉ s.decided :=
          Finset.disjoint_left.mp hwell.2 hvfrontier
        have hvNotOccupied : v ∉ s.occupied := fun hv ↦
          hvNotDecided (Finset.mem_union_left _ hv)
        have hvNotRejected : v ∉ s.rejected := fun hv ↦
          hvNotDecided (Finset.mem_union_right _ hv)
        have hvNotAcceptedHistory : v ∉ explorationHistoryAccepted s.history := by
          rw [← hconsistent.1]
          exact hvNotOccupied
        have hvNotRejectedHistory : v ∉ explorationHistoryRejected s.history := by
          rw [← hconsistent.2]
          exact hvNotRejected
        obtain ⟨u, huOccupied, huv⟩ := hopen.2.2 v hvfrontier
        have huAccepted : u ∈ explorationHistoryAccepted s.history := by
          rw [← hconsistent.1]
          exact huOccupied
        let EA := AdaptiveSiteExploration.cubicRegion d F root
        have hne : (EA.historyInletCandidates s.history v).Nonempty := by
          refine ⟨u, ?_⟩
          rw [AdaptiveSiteExploration.historyInletCandidates, Finset.mem_filter]
          refine ⟨huAccepted, ?_⟩
          simpa [EA, E, AdaptiveSiteExploration.cubicRegion, SiteExploration.toAdaptive] using huv
        let S' := step hd hmn root s.history v accepted p delta incremented X S
        have hcover' : OutgoingCoversUndecidedNeighbors
            (s.history ++ [(v, accepted)]) S' := by
          exact outgoingCoversUndecidedNeighbors_step hd hmn root s.history v accepted p delta
            incremented X S hcover hvNotAcceptedHistory hvNotRejectedHistory
              (by simpa [EA] using hne)
        have hwell' : (E.step (fun _ ↦ accepted) s).WellFormed :=
          E.step_wellFormed (fun _ ↦ accepted) hwell
        have hconsistent' : (E.step (fun _ ↦ accepted) s).HistoryConsistent :=
          siteStep_historyConsistent E (fun _ ↦ accepted) hconsistent
        have hopen' : E.OpenRootedAt root (E.step (fun _ ↦ accepted) s) :=
          E.step_openRootedAt (fun _ ↦ accepted) root hopen
        have hstepHistory : (E.step (fun _ ↦ accepted) s).history =
            s.history ++ [(v, accepted)] :=
          siteStep_history_eq_append_of_nextVertex_eq_some E s v accepted hnext
        have hih := ih (E.step (fun _ ↦ accepted) s) S' hwell' hconsistent' hopen'
          (by simpa [hstepHistory] using hcover')
        simpa [E, SiteExploration.replayStateFrom, replayFrom, S', hstepHistory] using hih

/-- Replay the suffix supplied to the initialized coarse-site oracle. -/
noncomputable def replay
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool)) :
    DynamicBlockHistoryState d F :=
  replayFrom hd hmn root p delta incremented X [(root, true)]
    (DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X)
      (canonicalSuffix root history)

/-- Every completed root replay carries the outgoing-table invariant through the canonical
chronological suffix.  In particular, all admissible next queries can recover a genuine parent
seed rather than the totalized dummy inlet. -/
theorem outgoingCoversUndecidedNeighbors_replay
    [NeZero d] (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool))
    (hX : X ∈ W.mixedExtensionPrefixSuccessEvent p radialIncremented delta
      incremented (rootExtensionDirectionOrder d).length) :
    OutgoingCoversUndecidedNeighbors
      ([(root, true)] ++ canonicalSuffix root history)
      (replay hd hmn W root p radialIncremented delta incremented X history) := by
  classical
  let E := cubicRegionSiteExploration d F root
  let S0 := DynamicBlockHistoryState.rooted W root p radialIncremented delta incremented X
  have hwell : E.initial.WellFormed := by
    simpa [E] using cubicRegionSiteExploration_initial_wellFormed d F root
  have hconsistent : E.initial.HistoryConsistent := by
    simp [E, cubicRegionSiteExploration, rootedSiteExploration,
      SiteExplorationState.HistoryConsistent, explorationHistoryAccepted,
      explorationHistoryRejected]
  have hopen : E.OpenRootedAt root E.initial := by
    simpa [E] using cubicRegionSiteExploration_initial_openRootedAt d F root
  have hcover : OutgoingCoversUndecidedNeighbors E.initial.history S0 := by
    simpa [E, S0, cubicRegionSiteExploration, rootedSiteExploration] using
      outgoingCoversUndecidedNeighbors_rooted (W := W) root p radialIncremented delta
        incremented X hX
  have hrun := outgoingCoversUndecidedNeighbors_replayFrom_chronologicalTrace
    hd hmn root p delta incremented X E.initial S0 history hwell hconsistent hopen hcover
  rw [root_cons_canonicalSuffix_eq_replayHistory]
  simpa [replay, canonicalSuffix_eq_chronologicalTraceFrom, E, S0,
    cubicRegionSiteExploration, rootedSiteExploration] using hrun

/-- Runtime of the next query after replaying the supplied suffix. -/
noncomputable def nextRuntime
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool)) (v : F) :
    LaterSiteRuntime d :=
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let queried := canonicalQueryFromFullHistory root fullHistory
  siteRuntime hd hmn root fullHistory queried p delta incremented X S

/-- Boolean answer of the concrete history-replayed non-root construction. -/
noncomputable def answer
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool)) (v : F) : Bool := by
  classical
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  exact decide <| LaterSiteRuntime.succeedsFrom hmn seed.physicalCenter
    (incomingDirection hd root fullHistory queried)
    (firstFlip hd root fullHistory queried S) unusedSecondFlip p delta incremented X
      (LaterSiteRuntime.initial S.source seed.physicalCenter) 0
      (siteDirectionOrder hd root fullHistory queried)

/-- The `j`-th source-faithful restart event for a queried site, padded by the sure event after
the history-dependent active schedule ends.  Padding lets every site use the uniform `4d`
probability budget without inventing geometric restarts in already-decided directions. -/
noncomputable def paddedStageSuccess
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (v : F) (j : ℕ) :
    Set (CubicEdge d → ℝ) :=
  {X |
    let S := replay hd hmn W root p radialIncremented delta incremented X history
    let fullHistory := [(root, true)] ++ canonicalSuffix root history
    let queried := canonicalQueryFromFullHistory root fullHistory
    let seed := inletSeed hd root fullHistory queried S
    let incoming := incomingDirection hd root fullHistory queried
    let first := firstFlip hd root fullHistory queried S
    let directions := siteDirectionOrder hd root fullHistory queried
    if hj : j < directions.length then
      let Rj := LaterSiteRuntime.runFrom hmn seed.physicalCenter incoming first
        unusedSecondFlip p delta incremented X
          (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 (directions.take j)
      X ∈ (Rj.restartQuery seed.physicalCenter incoming first unusedSecondFlip
        directions[j] j).successEvent m n p delta
    else True}

/-- The total runtime answer is exactly the conjunction of the padded `4d` stage family. -/
theorem answer_eq_finiteAdaptiveSuccessAnswer
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d) :
    answer hd hmn W root p radialIncremented delta incremented =
      AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer
        (paddedStageSuccess hd hmn W root p radialIncremented delta incremented) (4 * d) := by
  classical
  funext X history v
  apply Bool.eq_iff_iff.mpr
  let S := replay hd hmn W root p radialIncremented delta incremented X history
  let fullHistory := [(root, true)] ++ canonicalSuffix root history
  let queried := canonicalQueryFromFullHistory root fullHistory
  let seed := inletSeed hd root fullHistory queried S
  let incoming := incomingDirection hd root fullHistory queried
  let first := firstFlip hd root fullHistory queried S
  let directions := siteDirectionOrder hd root fullHistory queried
  have hlength : directions.length ≤ 4 * d := by
    simpa [directions] using siteDirectionOrder_length_le hd root fullHistory queried
  simpa only [answer, AdaptiveSiteExploration.finiteAdaptiveSuccessAnswer,
    AdaptiveSiteExploration.eventAdaptiveAnswer, decide_eq_true_eq,
    AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix, Set.mem_iInter,
    Finset.mem_range, paddedStageSuccess, Set.mem_setOf_eq, Nat.zero_add,
    S, fullHistory, queried, seed, incoming, first, directions] using
      (LaterSiteRuntime.succeedsFrom_iff_forall_padded hmn seed.physicalCenter incoming
        first unusedSecondFlip p delta incremented X
        (LaterSiteRuntime.initial S.source seed.physicalCenter) 0 (4 * d) directions hlength)

/-- Appending a successful coarse decision is exactly the preceding semantic history together
with all `4d` padded literal restart events.  This is the final-prefix identity consumed by the
non-circular initialized-program interface. -/
theorem adaptiveAnswerHistoryEvent_answer_append_true
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (history : List (F × Bool)) (v : F) :
    AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
        (answer hd hmn W root p radialIncremented delta incremented)
        (history ++ [(v, true)]) =
      AdaptiveSiteExploration.adaptiveAnswerHistoryEvent
          (answer hd hmn W root p radialIncremented delta incremented) history ∩
        AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix
          (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
          history v (4 * d) := by
  rw [AdaptiveSiteExploration.adaptiveAnswerHistoryEvent_append_singleton]
  congr 1
  ext X
  change answer hd hmn W root p radialIncremented delta incremented X history v = true ↔
    X ∈ AdaptiveSiteExploration.finiteAdaptiveSuccessPrefix
      (paddedStageSuccess hd hmn W root p radialIncremented delta incremented)
      history v (4 * d)
  rw [answer_eq_finiteAdaptiveSuccessAnswer]
  exact AdaptiveSiteExploration.eventAdaptiveAnswer_eq_true_iff _ _ _ _

@[simp]
theorem replayFrom_nil (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (prior : List (F × Bool))
    (S : DynamicBlockHistoryState d F) :
    replayFrom hd hmn root p delta incremented X prior S [] = S :=
  rfl

@[simp]
theorem replayFrom_cons (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (prior : List (F × Bool))
    (S : DynamicBlockHistoryState d F) (v : F) (accepted : Bool)
    (rest : List (F × Bool)) :
    replayFrom hd hmn root p delta incremented X prior S ((v, accepted) :: rest) =
      replayFrom hd hmn root p delta incremented X (prior ++ [(v, accepted)])
        (step hd hmn root prior v accepted p delta incremented X S) rest :=
  rfl

/-- Replay composition with the exact chronological prior carried into the second suffix. -/
theorem replayFrom_append (hd : 0 < d) (hmn : 2 * m ≤ n)
    (root : F) (p : I) (delta : ℝ) (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (prior : List (F × Bool))
    (S : DynamicBlockHistoryState d F) (suffix tail : List (F × Bool)) :
    replayFrom hd hmn root p delta incremented X prior S (suffix ++ tail) =
      replayFrom hd hmn root p delta incremented X (prior ++ suffix)
        (replayFrom hd hmn root p delta incremented X prior S suffix) tail := by
  induction suffix generalizing prior S with
  | nil => simp
  | cons entry suffix ih =>
      rcases entry with ⟨v, accepted⟩
      simp only [List.cons_append, replayFrom_cons]
      simpa [List.append_assoc] using ih (prior ++ [(v, accepted)])
        (step hd hmn root prior v accepted p delta incremented X S)

/-- A genuine next coarse answer extends the global replay by exactly one canonical runtime
step.  This is the induction equation needed for history-wide seed installation. -/
theorem replay_append_singleton_of_admissibleQuery
    (hd : 0 < d) (hmn : 2 * m ≤ n)
    (W : RootRadialSeedProfile d m n) (root : F)
    (p radialIncremented : I) (delta : ℝ)
    (incremented : RootExtensionThresholdPolicy d)
    (X : CubicEdge d → ℝ) (history : List (F × Bool)) (v : F) (accepted : Bool)
    (hadmissible : AdmissibleQuery root history v) :
    replay hd hmn W root p radialIncremented delta incremented X
        (history ++ [(v, accepted)]) =
      step hd hmn root ([(root, true)] ++ canonicalSuffix root history) v accepted
        p delta incremented X
        (replay hd hmn W root p radialIncremented delta incremented X history) := by
  rw [replay, canonicalSuffix_append_singleton_of_admissibleQuery
    root history v accepted hadmissible, replayFrom_append]
  rfl

end DynamicBlockHistoryReplay

end Percolation
