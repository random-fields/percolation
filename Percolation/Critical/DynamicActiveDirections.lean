import Percolation.Critical.DynamicSourceSchedule
import Percolation.Critical.ExplorationHistory

/-!
# Fresh coarse directions in the dynamic block exploration

A frontier site can have several previously accepted neighbours.  After choosing one inlet,
the Grimmett--Marstrand construction must not advertise every other geometric direction as a
fresh branch: a neighbour in that direction may already have been accepted or rejected through
another route.  This file records the exact finite set of non-parent directions whose endpoint
is still undecided.  Inactive slots may be padded by a probability-one stage, so the uniform
    fixed `4d` lower bound is unchanged.
-/

namespace Percolation

/-- Sites whose status has already been recorded by a chronological exploration history. -/
def explorationHistoryDecided {V : Type*} [DecidableEq V]
    (history : List (V × Bool)) : Finset V :=
  explorationHistoryAccepted history ∪ explorationHistoryRejected history

@[simp]
theorem mem_explorationHistoryDecided_iff
    {V : Type*} [DecidableEq V] {history : List (V × Bool)} {v : V} :
    v ∈ explorationHistoryDecided history ↔
      v ∈ explorationHistoryAccepted history ∨
        v ∈ explorationHistoryRejected history := by
  simp [explorationHistoryDecided]

/-- The endpoint of a signed step, when that endpoint remains in the induced coarse region. -/
noncomputable def coarseStep? {d : ℕ} (F : Set (Cubic d))
    (v : F) (a : CubicDirection d) : Option F := by
  classical
  exact if h : cubicStepFrom (v : Cubic d) a ∈ F then
    some ⟨cubicStepFrom (v : Cubic d) a, h⟩
  else none

theorem coarseStep?_eq_some_iff
    {d : ℕ} {F : Set (Cubic d)} {v w : F} {a : CubicDirection d} :
    coarseStep? F v a = some w ↔ cubicStepFrom (v : Cubic d) a = (w : Cubic d) := by
  classical
  unfold coarseStep?
  split_ifs with h
  · constructor
    · intro heq
      exact congrArg Subtype.val (Option.some.inj heq)
    · intro heq
      apply congrArg some
      exact Subtype.ext heq
  · constructor
    · simp
    · intro heq
      exact h (heq.symm ▸ w.property)

/-- Non-parent directions leading to an as-yet undecided vertex of the coarse region. -/
noncomputable def activeLaterSiteBranchDirections
    {d : ℕ} (F : Set (Cubic d)) (history : List (F × Bool)) (v : F)
    (incoming : CubicDirection d) : Finset (CubicDirection d) := by
  classical
  exact (laterSiteBranchDirections incoming).filter fun a ↦
    ∃ w : F, coarseStep? F v a = some w ∧
      w ∉ explorationHistoryDecided history

@[simp]
theorem mem_activeLaterSiteBranchDirections_iff
    {d : ℕ} {F : Set (Cubic d)} {history : List (F × Bool)} {v : F}
    {incoming a : CubicDirection d} :
    a ∈ activeLaterSiteBranchDirections F history v incoming ↔
      a ≠ reverseCubicDirection incoming ∧
        ∃ w : F, cubicStepFrom (v : Cubic d) a = (w : Cubic d) ∧
          w ∉ explorationHistoryDecided history := by
  classical
  simp only [activeLaterSiteBranchDirections, Finset.mem_filter,
    mem_laterSiteBranchDirections_iff]
  constructor
  · rintro ⟨ha, w, hstep, hw⟩
    exact ⟨ha, w, (coarseStep?_eq_some_iff.mp hstep), hw⟩
  · rintro ⟨ha, w, hstep, hw⟩
    exact ⟨ha, w, coarseStep?_eq_some_iff.mpr hstep, hw⟩

theorem activeLaterSiteBranchDirections_subset
    {d : ℕ} {F : Set (Cubic d)} (history : List (F × Bool)) (v : F)
    (incoming : CubicDirection d) :
    activeLaterSiteBranchDirections F history v incoming ⊆
      laterSiteBranchDirections incoming := by
  classical
  exact Finset.filter_subset _ _

theorem activeLaterSiteBranchDirections_card_le
    {d : ℕ} {F : Set (Cubic d)} (hd : 0 < d)
    (history : List (F × Bool)) (v : F) (incoming : CubicDirection d) :
    (activeLaterSiteBranchDirections F history v incoming).card ≤ 2 * d - 1 := by
  calc
    (activeLaterSiteBranchDirections F history v incoming).card ≤
        (laterSiteBranchDirections incoming).card :=
      Finset.card_le_card (activeLaterSiteBranchDirections_subset history v incoming)
    _ = 2 * d - 1 := laterSiteBranchDirections_card hd incoming

/-- Fully expanded active schedule: two inlet restarts, then a face-seed and link-up restart for
each fresh non-parent branch. -/
noncomputable def activeLaterSiteDirectionOrder
    {d : ℕ} {F : Set (Cubic d)} (history : List (F × Bool)) (v : F)
    (incoming : CubicDirection d) : List (CubicDirection d) :=
  incoming :: incoming ::
    (activeLaterSiteBranchDirections F history v incoming).toList.flatMap
      laterSiteBranchRestartPair

theorem activeLaterSiteDirectionOrder_length_le
    {d : ℕ} {F : Set (Cubic d)} (hd : 0 < d)
    (history : List (F × Bool)) (v : F) (incoming : CubicDirection d) :
    (activeLaterSiteDirectionOrder history v incoming).length ≤ 4 * d := by
  have hcard := activeLaterSiteBranchDirections_card_le hd history v incoming
  simp [activeLaterSiteDirectionOrder, laterSiteBranchRestartPair]
  omega

theorem mem_activeLaterSiteBranchDirections_target_not_accepted
    {d : ℕ} {F : Set (Cubic d)} {history : List (F × Bool)} {v : F}
    {incoming a : CubicDirection d}
    (ha : a ∈ activeLaterSiteBranchDirections F history v incoming) :
    ∀ w : F, cubicStepFrom (v : Cubic d) a = (w : Cubic d) →
      w ∉ explorationHistoryAccepted history := by
  intro w hstep hw
  obtain ⟨_ha, u, hu, huFresh⟩ := mem_activeLaterSiteBranchDirections_iff.mp ha
  have hwu : w = u := Subtype.ext (hstep.symm.trans hu)
  subst u
  exact huFresh (Finset.mem_union_left _ hw)

theorem mem_activeLaterSiteBranchDirections_target_not_rejected
    {d : ℕ} {F : Set (Cubic d)} {history : List (F × Bool)} {v : F}
    {incoming a : CubicDirection d}
    (ha : a ∈ activeLaterSiteBranchDirections F history v incoming) :
    ∀ w : F, cubicStepFrom (v : Cubic d) a = (w : Cubic d) →
      w ∉ explorationHistoryRejected history := by
  intro w hstep hw
  obtain ⟨_ha, u, hu, huFresh⟩ := mem_activeLaterSiteBranchDirections_iff.mp ha
  have hwu : w = u := Subtype.ext (hstep.symm.trans hu)
  subst u
  exact huFresh (Finset.mem_union_right _ hw)

end Percolation
