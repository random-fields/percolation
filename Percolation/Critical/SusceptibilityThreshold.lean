import Percolation.Critical.GhostConclusion

/-!
# Equality of the susceptibility and percolation thresholds

This file records the headline consequences of the Aizenman--Barsky proof: finite
susceptibility below the percolation threshold and Grimmett's equation (5.3),
`p_T = p_c`.
-/

namespace Percolation

open scoped ENNReal unitInterval

/-- Grimmett, Theorem 5.2.  The mean size of the origin cluster is finite below
the percolation threshold.  The two source proofs are exposed separately; this
headline declaration currently delegates to the completed ghost-field route. -/
theorem susceptibility_lt_top_of_lt_critical
    (d : ℕ) (hd : 2 ≤ d) (p : I)
    (hp : (p : ℝ) < cubicCriticalProbability d) :
    susceptibility d p < ⊤ :=
  susceptibility_lt_top_of_lt_critical_via_ghost d hd p hp

/-- The real representatives of unit-interval densities with finite
susceptibility form a nonempty set. -/
theorem susceptibilityFiniteSet_nonempty (d : ℕ) (hd : 2 ≤ d) :
    (((fun p : I ↦ (p : ℝ)) '' {p : I | susceptibility d p < ⊤}) : Set ℝ).Nonempty := by
  let p₀ : I := ⟨0, by simp⟩
  have hpc0 : 0 < cubicCriticalProbability d :=
    (one_div_pos.mpr (cubicConnectiveConstant_pos (by omega))).trans_le
      (connectiveConstant_inv_le_cubicCriticalProbability hd)
  exact ⟨0, p₀, susceptibility_lt_top_of_lt_critical d hd p₀ (by simpa [p₀]), rfl⟩

/-- The finite-susceptibility density set is bounded above by one. -/
theorem susceptibilityFiniteSet_bddAbove (d : ℕ) :
    BddAbove (((fun p : I ↦ (p : ℝ)) '' {p : I | susceptibility d p < ⊤}) : Set ℝ) := by
  refine ⟨1, ?_⟩
  rintro q ⟨p, _hp, rfl⟩
  exact p.property.2

/-- Every density of finite susceptibility is at most the percolation
threshold. -/
theorem density_le_criticalProbability_of_susceptibility_lt_top
    {d : ℕ} {p : I} (hp : susceptibility d p < ⊤) :
    (p : ℝ) ≤ cubicCriticalProbability d := by
  by_contra hnot
  have htheta : 0 < theta d p :=
    theta_pos_of_criticalProbability_lt (lt_of_not_ge hnot)
  have htop := susceptibility_eq_top_of_theta_pos htheta
  rw [htop] at hp
  exact (lt_irrefl _ hp)

/-- Grimmett, equation (5.3): the susceptibility threshold equals the
percolation threshold. -/
theorem susceptibilityThreshold_eq_criticalProbability
    (d : ℕ) (hd : 2 ≤ d) :
    susceptibilityThreshold d = cubicCriticalProbability d := by
  let S : Set ℝ :=
    ((fun p : I ↦ (p : ℝ)) '' {p : I | susceptibility d p < ⊤})
  have hSne : S.Nonempty := susceptibilityFiniteSet_nonempty d hd
  have hSbdd : BddAbove S := susceptibilityFiniteSet_bddAbove d
  apply le_antisymm
  · rw [susceptibilityThreshold]
    exact csSup_le hSne fun q hq ↦ by
      rcases hq with ⟨p, hp, rfl⟩
      exact density_le_criticalProbability_of_susceptibility_lt_top hp
  · rw [susceptibilityThreshold]
    let pc := cubicCriticalProbability d
    have hpc0 : 0 < pc := by
      dsimp only [pc]
      exact (one_div_pos.mpr (cubicConnectiveConstant_pos (by omega))).trans_le
        (connectiveConstant_inv_le_cubicCriticalProbability hd)
    have hpc1 : pc ≤ 1 := cubicCriticalProbability_le_one d
    have hzeroMem : (0 : ℝ) ∈ S := by
      let p₀ : I := ⟨0, by simp⟩
      exact ⟨p₀, susceptibility_lt_top_of_lt_critical d hd p₀ (by
        simpa [p₀, pc] using hpc0), rfl⟩
    have hSup0 : 0 ≤ sSup S := le_csSup hSbdd hzeroMem
    by_contra hnot
    have hSupPc : sSup S < pc := lt_of_not_ge hnot
    let q : ℝ := (sSup S + pc) / 2
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      linarith
    have hqpc : q < pc := by
      dsimp only [q]
      linarith
    let qI : I := ⟨q, hq0, hqpc.le.trans hpc1⟩
    have hqMem : q ∈ S := ⟨qI,
      susceptibility_lt_top_of_lt_critical d hd qI (by
        simpa [qI, pc] using hqpc), rfl⟩
    have hqSup : q ≤ sSup S := le_csSup hSbdd hqMem
    dsimp only [q] at hqSup
    linarith

#print axioms susceptibility_lt_top_of_lt_critical
#print axioms susceptibilityThreshold_eq_criticalProbability

end Percolation
