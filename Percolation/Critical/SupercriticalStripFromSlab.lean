import Percolation.Critical.SlabLimitAssembly
import Percolation.Critical.SupercriticalStripConclusion

/-!
# The Chapter 7 slab input for the supercritical finite-radius rate

This file is the narrow dependency boundary between Grimmett Chapters 7 and 8.  In dimension at
least three, slab critical-probability approximation supplies a slab that is supercritical at
`p`.  That slab lies in a finite-width coordinate strip, and coordinate symmetry rotates the
strip to the reference direction used in equations (8.43)--(8.48).
-/

namespace Percolation

open Set
open scoped unitInterval

/-- A width-`L` Grimmett slab is contained in a width-`L+1` coordinate strip along any of its
bounded coordinates. -/
theorem cubicSlab_subset_coordinateStrip
    {d L : ℕ} (i : Fin d) (hi : 2 ≤ i.val) :
    cubicSlab d L ⊆ cubicCoordinateStrip d i 0 (L + 1) := by
  intro x hx
  have hxi := hx i hi
  rw [mem_cubicCoordinateStrip]
  constructor
  · exact hxi.1
  · norm_num
    omega

/-- In dimension at least three, any supercritical slab produces a supercritical reference
coordinate strip. -/
theorem exists_coordinateStrip_critical_lt_of_slabCritical_lt
    {d L : ℕ} (hd : 3 ≤ d) {p : I}
    (hslab : slabCriticalProbability d L < (p : ℝ)) :
    ∃ k : ℕ, 0 < k ∧
      regionCriticalProbability d
        (cubicCoordinateStrip d ⟨0, by omega⟩ 0 k) < (p : ℝ) := by
  let i : Fin d := ⟨2, by omega⟩
  let i0 : Fin d := ⟨0, by omega⟩
  let e : Fin d ≃ Fin d := Equiv.swap i i0
  let k := L + 1
  have hsubset : cubicSlab d L ⊆ cubicCoordinateStrip d i 0 k := by
    exact cubicSlab_subset_coordinateStrip i (by simp [i])
  have hstrip_i : regionCriticalProbability d (cubicCoordinateStrip d i 0 k) <
      (p : ℝ) :=
    (regionCriticalProbability_anti hsubset).trans_lt (by
      simpa [slabCriticalProbability] using hslab)
  have himage : cubicGraphIsoRegion (cubicCoordinatePermutationIso e)
      (cubicCoordinateStrip d i 0 k) = cubicCoordinateStrip d i0 0 k := by
    simpa [e] using
      (cubicGraphIsoRegion_coordinatePermutation_coordinateStrip e i 0 k)
  have heq : regionCriticalProbability d (cubicCoordinateStrip d i0 0 k) =
      regionCriticalProbability d (cubicCoordinateStrip d i 0 k) := by
    rw [← himage]
    exact regionCriticalProbability_coordinatePermutation e
      (cubicCoordinateStrip d i 0 k)
  refine ⟨k, by simp [k], ?_⟩
  simpa [i0] using heq.trans_lt hstrip_i

/-- Slab approximation supplies a supercritical reference coordinate strip at every
`p>p_c`, in dimension at least three. -/
theorem exists_coordinateStrip_critical_lt_of_slabCriticalApproximation
    {d : ℕ} (hd : 3 ≤ d) (happrox : SlabCriticalApproximation d)
    {p : I} (hp : cubicCriticalProbability d < (p : ℝ)) :
    ∃ k : ℕ, 0 < k ∧
      regionCriticalProbability d
        (cubicCoordinateStrip d ⟨0, by omega⟩ 0 k) < (p : ℝ) := by
  let eta := ((p : ℝ) - cubicCriticalProbability d) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  obtain ⟨L, hL⟩ := happrox eta heta
  have hslab : slabCriticalProbability d L < (p : ℝ) := by
    apply hL.trans_lt
    dsimp [eta]
    linarith
  exact exists_coordinateStrip_critical_lt_of_slabCritical_lt hd hslab

/-- **Theorem 8.21 for `d≥3`, conditional exactly on the unfinished unconditional output of
Chapter 7 Theorem 7.2.** -/
theorem finiteClusterRadiusDecayRate_pos_of_critical_lt_of_slabCriticalApproximation
    {d : ℕ} (hd : 3 ≤ d) (happrox : SlabCriticalApproximation d)
    (p : I) (hp : cubicCriticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    0 < finiteClusterRadiusDecayRate d p := by
  obtain ⟨k, hk, hcrit⟩ :=
    exists_coordinateStrip_critical_lt_of_slabCriticalApproximation hd happrox hp
  exact finiteClusterRadiusDecayRate_pos_of_coordinateStrip_critical_lt
    (by omega) p hp1 hk hcrit

end Percolation
