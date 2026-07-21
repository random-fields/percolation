import Percolation.Extensions.LongRangePowerLaw

/-!
# Parameter families for one-dimensional power-law percolation

Grimmett's notation `θ(p, α, β)` fixes the nearest-neighbour density `p` but only specifies
the remaining profile asymptotically.  An asymptotic equivalence is not a probability measure.
This file therefore records the complete family as data and develops its critical-value/order
interface.  The deep block estimates establishing its endpoint phases are kept separate.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- A complete one-parameter family whose distance-one density is the parameter and whose
long bonds use the canonical inverse-power intensity. -/
structure LongRangePowerLawFamily (β α : ℝ) where
  profile : I → LongRangeProfile
  nearestNeighbour : ∀ q, profile q 1 = q
  powerLawTail : ∀ q n, 2 ≤ n →
    profile q n = longRangePowerLawTailProbability β α n

namespace LongRangePowerLawFamily

instance {β α : ℝ} : CoeFun (LongRangePowerLawFamily β α)
    fun _ ↦ I → LongRangeProfile :=
  ⟨LongRangePowerLawFamily.profile⟩

/-- The literal canonical family. -/
noncomputable def canonical (β α : ℝ) : LongRangePowerLawFamily β α where
  profile := fun q ↦ longRangePowerLawProfile q β α
  nearestNeighbour := fun q ↦ longRangePowerLawProfile_one q β α
  powerLawTail := fun q n hn ↦ longRangePowerLawProfile_of_two_le q β α hn

@[simp]
theorem canonical_apply (q : I) (β α : ℝ) :
    canonical β α q = longRangePowerLawProfile q β α := rfl

theorem profile_mono {β α : ℝ} (F : LongRangePowerLawFamily β α)
    {q r : I} (hqr : q ≤ r) : ∀ n, F q n ≤ F r n := by
  intro n
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simpa [F.nearestNeighbour] using hqr
  · rw [F.powerLawTail q (n + 2) (by omega),
      F.powerLawTail r (n + 2) (by omega)]

/-- Root percolation probability for a fully specified power-law family. -/
noncomputable def theta {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I) : ℝ :=
  longRangeTheta (F q)

theorem theta_nonneg {β α : ℝ} (F : LongRangePowerLawFamily β α) (q : I) :
    0 ≤ F.theta q :=
  measureReal_nonneg

theorem theta_mono {β α : ℝ} (F : LongRangePowerLawFamily β α) :
    Monotone F.theta := by
  intro q r hqr
  exact longRangeTheta_mono (F.profile_mono hqr)

/-- The real zero-phase set used in the definition of the nearest-neighbour threshold. -/
def criticalZeroSet {β α : ℝ} (F : LongRangePowerLawFamily β α) : Set ℝ :=
  (fun q : I ↦ (q : ℝ)) '' {q : I | F.theta q = 0}

/-- Critical nearest-neighbour density of a completely specified family. -/
noncomputable def criticalProbability {β α : ℝ}
    (F : LongRangePowerLawFamily β α) : ℝ :=
  sSup F.criticalZeroSet

theorem criticalZeroSet_bddAbove {β α : ℝ} (F : LongRangePowerLawFamily β α) :
    BddAbove F.criticalZeroSet := by
  refine ⟨1, ?_⟩
  rintro _ ⟨q, _hq, rfl⟩
  exact q.2.2

theorem criticalZeroSet_nonempty {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hzero : F.theta 0 = 0) :
    F.criticalZeroSet.Nonempty :=
  ⟨0, ⟨0, hzero, rfl⟩⟩

theorem criticalProbability_nonneg {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hzero : F.theta 0 = 0) :
    0 ≤ F.criticalProbability := by
  exact le_csSup (F.criticalZeroSet_bddAbove) ⟨0, hzero, rfl⟩

theorem criticalProbability_le_one {β α : ℝ} (F : LongRangePowerLawFamily β α)
    (hzero : F.theta 0 = 0) :
    F.criticalProbability ≤ 1 := by
  apply csSup_le (F.criticalZeroSet_nonempty hzero)
  rintro _ ⟨q, _hq, rfl⟩
  exact q.2.2

/-- Every parameter strictly below the defining supremum belongs to the zero phase. -/
theorem theta_eq_zero_of_lt_criticalProbability {β α : ℝ}
    (F : LongRangePowerLawFamily β α) (hzero : F.theta 0 = 0)
    {q : I} (hq : (q : ℝ) < F.criticalProbability) :
    F.theta q = 0 := by
  rw [criticalProbability] at hq
  obtain ⟨r, ⟨rI, hrzero, rfl⟩, hqr⟩ :=
    exists_lt_of_lt_csSup (F.criticalZeroSet_nonempty hzero) hq
  apply le_antisymm
  · exact (F.theta_mono (show q ≤ rI by exact_mod_cast hqr.le)).trans_eq hrzero
  · exact F.theta_nonneg q

/-- Every parameter strictly above the defining supremum belongs to the positive phase. -/
theorem theta_pos_of_criticalProbability_lt {β α : ℝ}
    (F : LongRangePowerLawFamily β α) {q : I}
    (hq : F.criticalProbability < (q : ℝ)) :
    0 < F.theta q := by
  apply lt_of_le_of_ne (F.theta_nonneg q)
  intro htheta
  have hmem : (q : ℝ) ∈ F.criticalZeroSet := ⟨q, htheta.symm, rfl⟩
  exact (not_le_of_gt hq) (le_csSup F.criticalZeroSet_bddAbove hmem)

/-- A vanishing parameter bounds the critical probability from below. -/
theorem le_criticalProbability_of_theta_eq_zero {β α : ℝ}
    (F : LongRangePowerLawFamily β α) {q : I} (hq : F.theta q = 0) :
    (q : ℝ) ≤ F.criticalProbability :=
  le_csSup F.criticalZeroSet_bddAbove ⟨q, hq, rfl⟩

/-- One positive parameter bounds the critical probability strictly below one. -/
theorem criticalProbability_lt_one_of_theta_pos {β α : ℝ}
    (F : LongRangePowerLawFamily β α) {q : I} (hq1 : (q : ℝ) < 1)
    (hq : 0 < F.theta q) :
    F.criticalProbability < 1 := by
  apply lt_of_le_of_lt ?_ hq1
  by_cases hne : F.criticalZeroSet.Nonempty
  · apply csSup_le hne
    rintro r ⟨rI, hrzero, rfl⟩
    by_contra hnot
    have hqr : q ≤ rI := by exact_mod_cast le_of_not_ge hnot
    have := F.theta_mono hqr
    rw [hrzero] at this
    exact (not_lt_of_ge this) hq
  · rw [criticalProbability, Set.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Real.sSup_empty] using q.2.1

end LongRangePowerLawFamily

end Percolation
