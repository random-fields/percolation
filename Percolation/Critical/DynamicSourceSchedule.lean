import Percolation.Critical.DynamicFramedRestartPartition
import Percolation.Critical.DynamicRevealBudget

/-!
# Source-order schedules for the Grimmett--Marstrand construction

The schedule on pp. 158--162 is not merely a list of `2d+1` arbitrary restarts.  The root has
one post-radial extension in each signed direction.  A later site first performs two inlet
extensions and then branches in every direction except back toward its parent.  These finite
orders are made explicit here before any probability or interval-fiber construction is attached
to them.
-/

namespace Percolation

/-- Reverse a signed cubic direction. -/
def reverseCubicDirection {d : ℕ} (a : CubicDirection d) : CubicDirection d :=
  (a.1, !a.2)

@[simp]
theorem reverseCubicDirection_fst {d : ℕ} (a : CubicDirection d) :
    (reverseCubicDirection a).1 = a.1 :=
  rfl

@[simp]
theorem reverseCubicDirection_snd {d : ℕ} (a : CubicDirection d) :
    (reverseCubicDirection a).2 = !a.2 :=
  rfl

@[simp]
theorem reverseCubicDirection_reverse {d : ℕ} (a : CubicDirection d) :
    reverseCubicDirection (reverseCubicDirection a) = a := by
  rcases a with ⟨i, b⟩
  cases b <;> rfl

theorem reverseCubicDirection_ne {d : ℕ} (a : CubicDirection d) :
    reverseCubicDirection a ≠ a := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [reverseCubicDirection]

theorem cubicStepFrom_reverse {d : ℕ} (x : Cubic d) (a : CubicDirection d) :
    cubicStepFrom (cubicStepFrom x a) (reverseCubicDirection a) = x := by
  rcases a with ⟨i, b⟩
  cases b
  · exact cubicStepFrom_neg_pos x i
  · exact cubicStepFrom_pos_neg x i

/-- Directions in which a non-root site branches after entering along `incoming`: every signed
direction except the edge leading back to its parent. -/
noncomputable def laterSiteBranchDirections {d : ℕ}
    (incoming : CubicDirection d) : Finset (CubicDirection d) :=
  Finset.univ.erase (reverseCubicDirection incoming)

@[simp]
theorem mem_laterSiteBranchDirections_iff {d : ℕ}
    {incoming a : CubicDirection d} :
    a ∈ laterSiteBranchDirections incoming ↔ a ≠ reverseCubicDirection incoming := by
  simp [laterSiteBranchDirections]

theorem laterSiteBranchDirections_card {d : ℕ} (hd : 0 < d)
    (incoming : CubicDirection d) :
    (laterSiteBranchDirections incoming).card = 2 * d - 1 := by
  rw [laterSiteBranchDirections, Finset.card_erase_of_mem (by simp)]
  simp [CubicDirection, Fintype.card_prod]
  omega

/-- Literal later-site direction order: two inlet extensions, then the `2d-1` non-backtracking
branches. -/
noncomputable def laterSiteDirectionOrder {d : ℕ}
    (incoming : CubicDirection d) : List (CubicDirection d) :=
  incoming :: incoming :: (laterSiteBranchDirections incoming).toList

@[simp]
theorem laterSiteDirectionOrder_head {d : ℕ} (incoming : CubicDirection d) :
    (laterSiteDirectionOrder incoming).head? = some incoming := by
  simp [laterSiteDirectionOrder]

@[simp]
theorem laterSiteDirectionOrder_getElem_one {d : ℕ} (incoming : CubicDirection d) :
    (laterSiteDirectionOrder incoming)[1]'(by simp [laterSiteDirectionOrder]) = incoming := by
  simp [laterSiteDirectionOrder]

theorem laterSiteDirectionOrder_length {d : ℕ} (hd : 0 < d)
    (incoming : CubicDirection d) :
    (laterSiteDirectionOrder incoming).length = 2 * d + 1 := by
  simp [laterSiteDirectionOrder, laterSiteBranchDirections_card hd]
  omega

/-! The book abbreviates each later-site branch as one operation.  In the underlying
Grimmett--Marstrand construction it has two restart applications: first produce a suitably
steered face seed, then link that seed into the adjacent half-way box.  The distinction is
essential for the spatial invariant and gives the source's safe `4d` bound. -/

/-- Two restart directions for one outgoing branch: the face-seed step and its link-up. -/
def laterSiteBranchRestartPair {d : ℕ} (a : CubicDirection d) : List (CubicDirection d) :=
  [a, a]

/-- Fully expanded later-site restart order from the original Grimmett--Marstrand proof. -/
noncomputable def laterSiteRestartDirectionOrder {d : ℕ}
    (incoming : CubicDirection d) : List (CubicDirection d) :=
  incoming :: incoming ::
    (laterSiteBranchDirections incoming).toList.flatMap laterSiteBranchRestartPair

theorem laterSiteRestartDirectionOrder_length {d : ℕ} (hd : 0 < d)
    (incoming : CubicDirection d) :
    (laterSiteRestartDirectionOrder incoming).length = 4 * d := by
  simp [laterSiteRestartDirectionOrder, laterSiteBranchRestartPair,
    laterSiteBranchDirections_card hd]
  omega

/-- Literal order of the post-radial root extensions. -/
noncomputable def rootExtensionDirectionOrder (d : ℕ) : List (CubicDirection d) :=
  (Finset.univ : Finset (CubicDirection d)).toList

@[simp]
theorem rootExtensionDirectionOrder_nodup (d : ℕ) :
    (rootExtensionDirectionOrder d).Nodup := by
  exact Finset.nodup_toList _

@[simp]
theorem rootExtensionDirectionOrder_length (d : ℕ) :
    (rootExtensionDirectionOrder d).length = 2 * d := by
  simp [rootExtensionDirectionOrder, CubicDirection, Fintype.card_prod, Nat.mul_comm]

/-- Support schedule of the `2d` root extensions. -/
noncomputable def rootExtensionSupportSchedule {d : ℕ} {iota : Type*}
    [DecidableEq iota] (support : CubicDirection d → Finset iota) :
    FiniteRevealSchedule iota where
  stages := (rootExtensionDirectionOrder d).map support

@[simp]
theorem rootExtensionSupportSchedule_length {d : ℕ} {iota : Type*}
    [DecidableEq iota] (support : CubicDirection d → Finset iota) :
    (rootExtensionSupportSchedule support).stages.length = 2 * d := by
  simp [rootExtensionSupportSchedule]

theorem rootExtensionSupportSchedule_hasOverlapBound {d : ℕ} {iota : Type*}
    [DecidableEq iota] (support : CubicDirection d → Finset iota) :
    (rootExtensionSupportSchedule support).HasOverlapBound (2 * d + 1) := by
  apply FiniteRevealSchedule.hasOverlapBound_of_length_le
  simp [rootExtensionSupportSchedule]

/-- Support schedule in the exact later-site order. -/
noncomputable def laterSiteSupportSchedule {d : ℕ} {iota : Type*}
    [DecidableEq iota] (incoming : CubicDirection d)
    (firstInlet secondInlet : Finset iota)
    (branch : CubicDirection d → Finset iota) : FiniteRevealSchedule iota where
  stages := firstInlet :: secondInlet ::
    (laterSiteBranchDirections incoming).toList.map branch

theorem laterSiteSupportSchedule_length {d : ℕ} {iota : Type*}
    [DecidableEq iota] (hd : 0 < d) (incoming : CubicDirection d)
    (firstInlet secondInlet : Finset iota)
    (branch : CubicDirection d → Finset iota) :
    (laterSiteSupportSchedule incoming firstInlet secondInlet branch).stages.length =
      2 * d + 1 := by
  simp [laterSiteSupportSchedule, laterSiteBranchDirections_card hd]
  omega

theorem laterSiteSupportSchedule_hasOverlapBound {d : ℕ} {iota : Type*}
    [DecidableEq iota] (hd : 0 < d) (incoming : CubicDirection d)
    (firstInlet secondInlet : Finset iota)
    (branch : CubicDirection d → Finset iota) :
    (laterSiteSupportSchedule incoming firstInlet secondInlet branch).HasOverlapBound
      (2 * d + 1) := by
  apply FiniteRevealSchedule.hasOverlapBound_of_length_le
  rw [laterSiteSupportSchedule_length hd]

/-- Steering mask for a branch leaving a non-root site: in the incoming coordinate, choose the
half-space pointing away from the parent.  The exit coordinate itself is controlled by
`outgoing`, so the mask is relevant only when the two axes differ. -/
def awayFromInletTransverseFlip {d : ℕ}
    (incoming outgoing : CubicDirection d) : Fin d → Bool :=
  fun j ↦ decide (j ≠ outgoing.1 ∧ j = incoming.1 ∧ incoming.2 = false)

theorem awayFromInletTransverseFlip_incoming_of_distinct_axis
    {d : ℕ} {incoming outgoing : CubicDirection d}
    (haxis : incoming.1 ≠ outgoing.1) :
    awayFromInletTransverseFlip incoming outgoing incoming.1 = !incoming.2 := by
  cases h : incoming.2 <;>
    simp [awayFromInletTransverseFlip, haxis, h]

end Percolation
