import Percolation.Critical.DynamicBlockGeometry

/-!
# Reveal-threshold accounting for dynamic renormalization

Equations (7.27), (7.31)--(7.34) repeatedly increase an edge's lower reveal threshold by the
sprinkling increment.  This file makes the accounting finite and explicit.  The geometric block
construction must later prove the relevant overlap bound; no overlap claim is assumed silently.
-/

namespace Percolation

open scoped BigOperators

/-- Finite list of supports on which successive restart steps may spend one threshold
increment. -/
structure FiniteRevealSchedule (iota : Type*) where
  stages : List (Finset iota)

namespace FiniteRevealSchedule

variable {iota : Type*} [DecidableEq iota]

/-- Number of reveal stages containing the coordinate `e`. -/
def multiplicity (S : FiniteRevealSchedule iota) (e : iota) : ℕ :=
  (S.stages.filter fun E => e ∈ E).length

@[simp]
theorem multiplicity_nil (e : iota) :
    (⟨[]⟩ : FiniteRevealSchedule iota).multiplicity e = 0 :=
  rfl

@[simp]
theorem multiplicity_cons (E : Finset iota) (stages : List (Finset iota)) (e : iota) :
    (⟨E :: stages⟩ : FiniteRevealSchedule iota).multiplicity e =
      (if e ∈ E then 1 else 0) + (⟨stages⟩ : FiniteRevealSchedule iota).multiplicity e := by
  by_cases he : e ∈ E
  · simp [multiplicity, he, Nat.add_comm]
  · simp [multiplicity, he]

/-- Every coordinate is charged at most `b` times. -/
def HasOverlapBound (S : FiniteRevealSchedule iota) (b : ℕ) : Prop :=
  ∀ e, S.multiplicity e ≤ b

/-- Real threshold obtained from a background density after all scheduled increments. -/
def accumulatedThreshold
    (S : FiniteRevealSchedule iota) (p delta : ℝ) (e : iota) : ℝ :=
  p + S.multiplicity e * delta

theorem accumulatedThreshold_nil (p delta : ℝ) (e : iota) :
    (⟨[]⟩ : FiniteRevealSchedule iota).accumulatedThreshold p delta e = p := by
  simp [accumulatedThreshold]

theorem accumulatedThreshold_cons_of_mem
    (E : Finset iota) (stages : List (Finset iota)) {e : iota} (he : e ∈ E)
    (p delta : ℝ) :
    (⟨E :: stages⟩ : FiniteRevealSchedule iota).accumulatedThreshold p delta e =
      (⟨stages⟩ : FiniteRevealSchedule iota).accumulatedThreshold p delta e + delta := by
  simp [accumulatedThreshold, he]
  ring

theorem accumulatedThreshold_cons_of_notMem
    (E : Finset iota) (stages : List (Finset iota)) {e : iota} (he : e ∉ E)
    (p delta : ℝ) :
    (⟨E :: stages⟩ : FiniteRevealSchedule iota).accumulatedThreshold p delta e =
      (⟨stages⟩ : FiniteRevealSchedule iota).accumulatedThreshold p delta e := by
  simp [accumulatedThreshold, he]

theorem accumulatedThreshold_mono_append_left
    (S T : FiniteRevealSchedule iota) (p delta : ℝ) (hdelta : 0 ≤ delta) (e : iota) :
    S.accumulatedThreshold p delta e ≤
      (⟨S.stages ++ T.stages⟩ : FiniteRevealSchedule iota).accumulatedThreshold p delta e := by
  rw [accumulatedThreshold, accumulatedThreshold]
  gcongr
  simp [multiplicity, List.filter_append]

/-- Abstract form of (7.34): bounded overlap bounds every accumulated threshold. -/
theorem accumulatedThreshold_le_of_overlapBound
    (S : FiniteRevealSchedule iota) {b : ℕ} (hS : S.HasOverlapBound b)
    (p delta : ℝ) (hdelta : 0 ≤ delta) (e : iota) :
    S.accumulatedThreshold p delta e ≤ p + b * delta := by
  rw [accumulatedThreshold]
  gcongr
  exact_mod_cast hS e

/-- If the increment is budgeted as `eta/b`, an overlap bound `b` spends at most `eta` in
total.  The case `b=0` is handled separately to avoid totalized division. -/
theorem accumulatedThreshold_le_add_budget
    (S : FiniteRevealSchedule iota) {b : ℕ} (hb : 0 < b)
    (hS : S.HasOverlapBound b) (p eta : ℝ) (heta : 0 ≤ eta) (e : iota) :
    S.accumulatedThreshold p (eta / b) e ≤ p + eta := by
  calc
    S.accumulatedThreshold p (eta / b) e ≤ p + b * (eta / b) :=
      S.accumulatedThreshold_le_of_overlapBound hS p (eta / b)
        (div_nonneg heta (Nat.cast_nonneg b)) e
    _ = p + eta := by
      field_simp

/-- Source specialization: one inlet plus all `2d` outgoing directions gives the accounting
budget `2d+1`.  The later steering proof must establish this overlap bound for its concrete
schedule. -/
theorem accumulatedThreshold_le_add_of_grimmettMarstrandOverlap
    (S : FiniteRevealSchedule iota) (d : ℕ)
    (hS : S.HasOverlapBound (2 * d + 1))
    (p eta : ℝ) (heta : 0 ≤ eta) (e : iota) :
    S.accumulatedThreshold p (eta / (2 * d + 1)) e ≤ p + eta := by
  simpa [Nat.cast_add, Nat.cast_mul] using
    S.accumulatedThreshold_le_add_budget (by omega) hS p eta heta e

/-- A coordinate cannot occur in more filtered stages than the total number of stages. -/
theorem multiplicity_le_stages_length (S : FiniteRevealSchedule iota) (e : iota) :
    S.multiplicity e ≤ S.stages.length := by
  unfold multiplicity
  exact List.length_filter_le _ _

theorem hasOverlapBound_of_length_le
    (S : FiniteRevealSchedule iota) {b : ℕ} (h : S.stages.length ≤ b) :
    S.HasOverlapBound b :=
  fun e => (S.multiplicity_le_stages_length e).trans h

/-- One inlet support followed by one support for every signed outgoing direction. -/
noncomputable def incidentDirectionSchedule
    (d : ℕ) (inlet : Finset iota)
    (outgoing : CubicDirection d → Finset iota) : FiniteRevealSchedule iota where
  stages := inlet :: (Finset.univ : Finset (CubicDirection d)).toList.map outgoing

omit [DecidableEq iota] in
@[simp] theorem incidentDirectionSchedule_stages_length
    (d : ℕ) (inlet : Finset iota)
    (outgoing : CubicDirection d → Finset iota) :
    (incidentDirectionSchedule d inlet outgoing).stages.length = 2 * d + 1 := by
  classical
  simp [incidentDirectionSchedule, Nat.mul_comm]

/-- The literal source overlap budget: even without using geometry, one inlet plus the `2d`
signed direction supports can charge an edge at most `2d+1` times. -/
theorem incidentDirectionSchedule_hasOverlapBound
    (d : ℕ) (inlet : Finset iota)
    (outgoing : CubicDirection d → Finset iota) :
    (incidentDirectionSchedule d inlet outgoing).HasOverlapBound (2 * d + 1) := by
  apply hasOverlapBound_of_length_le
  simp

end FiniteRevealSchedule

end Percolation
