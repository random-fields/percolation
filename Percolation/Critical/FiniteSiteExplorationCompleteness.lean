import Percolation.Critical.FiniteExplorationTermination
import Percolation.Critical.RootedSiteExploration

/-!
# Completeness of finite rooted site explorations

A finite rooted exploration does not merely construct an open connected set.  Once its frontier
is empty, it has queried every site adjacent to that set, so the accepted set is exactly the
root's open-site component.  This file records the two inductive invariants needed for that
statement: recorded answers agree with the site configuration, and every neighbor of an accepted
site is either decided or still on the frontier.
-/

namespace Percolation

namespace SiteExplorationState

variable {V : Type*} [DecidableEq V]

/-- Accepted sites are open and rejected sites are closed in `η`. -/
def AnswersAgree (s : SiteExplorationState V) (η : Set V) : Prop :=
  (∀ v ∈ s.occupied, v ∈ η) ∧ ∀ v ∈ s.rejected, v ∉ η

end SiteExplorationState

namespace SiteExploration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

/-- Every neighbor of an accepted site is already decided or remains eligible to be queried. -/
def FrontierClosed (E : SiteExploration V) (s : SiteExplorationState V) : Prop :=
  ∀ u ∈ s.occupied, E.neighbors u ⊆ s.decided ∪ s.frontier

theorem step_answersAgree (E : SiteExploration V) (η : Set V)
    {s : SiteExplorationState V} (hs : s.AnswersAgree η) :
    (E.step (configurationAnswer η) s).AnswersAgree η := by
  classical
  unfold SiteExplorationState.AnswersAgree at hs ⊢
  unfold SiteExploration.step
  split
  · exact hs
  next v hnext =>
    split <;> rename_i hv
    · constructor
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact (configurationAnswer_eq_true_iff η _).mp hv
        · exact hs.1 z hz
      · exact hs.2
    · constructor
      · exact hs.1
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact (configurationAnswer_eq_false_iff η _).mp (Bool.eq_false_of_not_eq_true hv)
        · exact hs.2 z hz

theorem stateAfter_answersAgree (E : SiteExploration V) (η : Set V)
    (hinitial : E.initial.AnswersAgree η) (n : ℕ) :
    (E.stateAfter (configurationAnswer η) n).AnswersAgree η := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_answersAgree η ih

theorem step_frontierClosed (E : SiteExploration V) (answer : V → Bool)
    {s : SiteExplorationState V} (hs : E.FrontierClosed s) :
    E.FrontierClosed (E.step answer s) := by
  classical
  unfold FrontierClosed at hs ⊢
  unfold SiteExploration.step
  split
  · exact hs
  next v hnext =>
    have hvfront : v ∈ s.frontier := mem_frontier_of_nextVertex_eq_some hnext
    split
    · intro u hu z hzu
      rw [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · by_cases hzdec : z ∈ insert u s.occupied ∪ s.rejected
        · exact Finset.mem_union_left _ hzdec
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_right _ hzu, hzdec⟩)
      · have hzold := hs u hu hzu
        rw [Finset.mem_union] at hzold
        rcases hzold with hzdec | hzfront
        · exact Finset.mem_union_left _ <| by
            rcases Finset.mem_union.mp hzdec with hzocc | hzrej
            · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hzocc)
            · exact Finset.mem_union_right _ hzrej
        · by_cases hzv : z = v
          · subst z
            exact Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_insert_self v s.occupied))
          · by_cases hzdec : z ∈ insert v s.occupied ∪ s.rejected
            · exact Finset.mem_union_left _ hzdec
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
                ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzv, hzfront⟩), hzdec⟩)
    · intro u hu z hzu
      have hzold := hs u hu hzu
      rw [Finset.mem_union] at hzold
      rcases hzold with hzdec | hzfront
      · exact Finset.mem_union_left _ <| by
          rcases Finset.mem_union.mp hzdec with hzocc | hzrej
          · exact Finset.mem_union_left _ hzocc
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hzrej)
      · by_cases hzv : z = v
        · subst z
          exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_insert_self v s.rejected))
        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzv, hzfront⟩)

theorem stateAfter_frontierClosed (E : SiteExploration V) (answer : V → Bool)
    (hinitial : E.FrontierClosed E.initial) (n : ℕ) :
    E.FrontierClosed (E.stateAfter answer n) := by
  induction n with
  | zero => exact hinitial
  | succ n ih => exact E.step_frontierClosed answer ih

theorem mem_occupied_of_open_walk_of_frontier_eq_empty
    (E : SiteExploration V) (η : Set V) {s : SiteExplorationState V}
    (hagree : s.AnswersAgree η) (hclosed : E.FrontierClosed s)
    (hfrontier : s.frontier = ∅) {x y : V} (hx : x ∈ s.occupied)
    (w : E.graph.Walk x y) (hw : ∀ z ∈ w.support, z ∈ η) :
    y ∈ s.occupied := by
  induction w with
  | nil => exact hx
  | @cons x y z hxy w ih =>
      have hyη : y ∈ η := hw y (by simp)
      have hyStatus := hclosed x hx ((E.mem_neighbors).mpr hxy)
      have hyDecided : y ∈ s.decided := by
        simpa [hfrontier] using hyStatus
      have hyOccupied : y ∈ s.occupied := by
        rcases Finset.mem_union.mp hyDecided with hyOccupied | hyRejected
        · exact hyOccupied
        · exact False.elim (hagree.2 y hyRejected hyη)
      exact ih hyOccupied fun a ha ↦ hw a (by simp [ha])

/-- At exhaustion, a rooted answer-consistent exploration has found the whole open component. -/
theorem occupied_eq_siteOpenCluster_of_frontier_eq_empty
    (E : SiteExploration V) (η : Set V) (root : V) {s : SiteExplorationState V}
    (hrooted : E.OpenRootedAt root s) (hagree : s.AnswersAgree η)
    (hclosed : E.FrontierClosed s) (hfrontier : s.frontier = ∅) :
    (s.occupied : Set V) = siteOpenCluster E.graph η root := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := hrooted.2.1 v hv
    exact ⟨w, fun z hz ↦ hagree.1 z (hw z hz)⟩
  · rintro ⟨w, hw⟩
    exact E.mem_occupied_of_open_walk_of_frontier_eq_empty η hagree hclosed hfrontier
      hrooted.1 w hw

end SiteExploration

section Rooted

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

omit [Fintype V] in
theorem rootedSiteExploration_initial_answersAgree
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    {root : V} {η : Set V} (hroot : root ∈ η) :
    (rootedSiteExploration G neighbors mem_neighbors root).initial.AnswersAgree η := by
  constructor
  · intro v hv
    have hvroot : v = root := by
      simpa [rootedSiteExploration] using hv
    exact hvroot.symm ▸ hroot
  · simp [rootedSiteExploration]

omit [Fintype V] in
theorem rootedSiteExploration_initial_frontierClosed
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) :
    (rootedSiteExploration G neighbors mem_neighbors root).FrontierClosed
      (rootedSiteExploration G neighbors mem_neighbors root).initial := by
  intro u hu z hzu
  have huroot : u = root := by
    simpa [rootedSiteExploration] using hu
  subst u
  simp [rootedSiteExploration]
  exact Or.inr hzu

/-- A finite rooted exploration, run for `|V|` steps, exactly returns the root's open cluster. -/
theorem rootedSiteExploration_stateAfter_card_occupied_eq_siteOpenCluster
    (G : SimpleGraph V) (neighbors : V → Finset V)
    (mem_neighbors : ∀ {x y}, y ∈ neighbors x ↔ G.Adj x y)
    (root : V) (η : Set V) (hroot : root ∈ η) :
    (((rootedSiteExploration G neighbors mem_neighbors root).stateAfter
      (configurationAnswer η) (Fintype.card V)).occupied : Set V) =
        siteOpenCluster G η root := by
  let E := rootedSiteExploration G neighbors mem_neighbors root
  apply E.occupied_eq_siteOpenCluster_of_frontier_eq_empty η root
  · exact E.stateAfter_openRootedAt (configurationAnswer η) root
      (rootedSiteExploration_initial_openRootedAt G neighbors mem_neighbors root) _
  · exact E.stateAfter_answersAgree η
      (rootedSiteExploration_initial_answersAgree G neighbors mem_neighbors hroot) _
  · exact E.stateAfter_frontierClosed (configurationAnswer η)
      (rootedSiteExploration_initial_frontierClosed G neighbors mem_neighbors root) _
  · exact E.stateAfter_card_frontier_eq_empty (configurationAnswer η)
      (rootedSiteExploration_initial_wellFormed G neighbors mem_neighbors root)

end Rooted

end Percolation
