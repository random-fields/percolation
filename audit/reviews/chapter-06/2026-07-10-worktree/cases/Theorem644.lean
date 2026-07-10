import Percolation.Critical.TwoPoint

/-! Application and endpoint tests for Grimmett, Theorem 6.44. -/

namespace Chapter6Review

open Percolation Filter
open scoped unitInterval

/-- The source constant is chosen before the density, so it depends on `d` but not on `p`. -/
example (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : I), 0 < (p : ℝ) → ∀ n : ℕ, 0 < n →
      c * (p : ℝ) / (n : ℝ) ^ (4 * (d - 1)) *
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) ≤
          twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ∧
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n) ≤
          Real.exp (-(n : ℝ) * boxRadiusDecayRate d p) := by
  exact twoPointConnectivity_axis_twoSided_decay d (by omega)

/-- The rate in the axis limit is exactly the box-radius rate, not a second opaque constant. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    Tendsto (fun n : ℕ ↦
      -Real.log (twoPointConnectivity d p cubicOrigin (cubicAxisVertex d n)) / n)
      atTop (nhds (boxRadiusDecayRate d p)) := by
  exact twoPointConnectivity_axis_logRate_tendsto (by omega) hp

/-- At the first positive distance the lower source factor contains one factor of `p`; the
radius-zero junk value is excluded by the theorem's `0 < n` input. -/
example (d : ℕ) (hd : 2 ≤ d) (p : I) (hp : 0 < (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      c * (p : ℝ) * Real.exp (-boxRadiusDecayRate d p) ≤
        twoPointConnectivity d p cubicOrigin (cubicAxisVertex d 1) := by
  obtain ⟨c, hc, h⟩ := twoPointConnectivity_axis_twoSided_decay d (by omega)
  refine ⟨c, hc, ?_⟩
  simpa using (h p hp 1 (by omega)).1

end Chapter6Review
