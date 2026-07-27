import Percolation.Critical.AdaptiveExploration

/-!
# First acceptance times in an adaptive site exploration

Every limiting occupied vertex outside the initial occupied set was inserted at one concrete
finite query.  This elementary extraction is used by the dynamic block construction to attach
the selected inlet seed from that query to the limiting coarse vertex.
-/

namespace Percolation

namespace AdaptiveSiteExploration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

/-- A non-initial vertex in the limiting occupied set has a finite successful query time. -/
theorem exists_acceptance_step_of_mem_occupiedLimit
    (E : AdaptiveSiteExploration V)
    (answer : List (V × Bool) → V → Bool) {v : V}
    (hv : v ∈ E.occupiedLimit answer) (hvInitial : v ∉ E.initial.occupied) :
    ∃ n : ℕ,
      SiteExploration.nextVertex (E.stateAfter answer n) = some v ∧
        answer (E.stateAfter answer n).history v = true := by
  classical
  let P : ℕ → Prop := fun n ↦ v ∈ (E.stateAfter answer n).occupied
  have hP : ∃ n, P n := hv
  let first := Nat.find hP
  have hfirst : P first := Nat.find_spec hP
  have hfirstNe : first ≠ 0 := by
    intro hzero
    apply hvInitial
    simpa [first, P, hzero, AdaptiveSiteExploration.stateAfter] using hfirst
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hfirstNe
  have hn' : Nat.find hP = n + 1 := by simpa [first] using hn
  rw [hn] at hfirst
  have hprev : v ∉ (E.stateAfter answer n).occupied := by
    intro hvn
    have hle : Nat.find hP ≤ n := Nat.find_min' hP hvn
    omega
  have hnextMem : v ∈
      (E.step answer (E.stateAfter answer n)).occupied := by
    simpa [AdaptiveSiteExploration.stateAfter] using hfirst
  unfold AdaptiveSiteExploration.step at hnextMem
  split at hnextMem
  · exact (hprev hnextMem).elim
  next u hnext =>
    split at hnextMem
    next haccepted =>
      have hvu : v = u := by
        rw [Finset.mem_insert] at hnextMem
        rcases hnextMem with hvu | hvOld
        · exact hvu
        · exact (hprev hvOld).elim
      subst u
      exact ⟨n, hnext, haccepted⟩
    next _hrejected =>
      exact (hprev hnextMem).elim

end AdaptiveSiteExploration

end Percolation
