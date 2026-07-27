import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic asymptotic laws

Grimmett writes `aₙ ≈ bₙ` when `log aₙ / log bₙ → 1`.  The normalized-log formulation below
is preferable for theorem statements because it exposes the geometric scale and avoids hiding
the sign of a decay rate.
-/

namespace Percolation

open Filter
open scoped Topology

/-- Grimmett's logarithmic equivalence `aₙ ≈ bₙ`. -/
def LogAsymptotic (a b : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ Real.log (a n) / Real.log (b n)) atTop (𝓝 1)

/-- A probability sequence has logarithmic decay rate `c` at scale `s`. -/
def HasNormalizedLogRate (a s : ℕ → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun n ↦ -Real.log (a n) / s n) atTop (𝓝 c)

theorem hasNormalizedLogRate_iff_logAsymptotic_exp_neg
    {a s : ℕ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hs : ∀ᶠ n in atTop, s n ≠ 0) :
    HasNormalizedLogRate a s c ↔
      LogAsymptotic a (fun n ↦ Real.exp (-c * s n)) := by
  have heq : ∀ᶠ n in atTop,
      Real.log (a n) / Real.log (Real.exp (-c * s n)) =
        (-Real.log (a n) / s n) / c := by
    filter_upwards [hs] with n hsn
    rw [Real.log_exp]
    field_simp
  constructor
  · intro h
    rw [LogAsymptotic]
    apply Tendsto.congr' (heq.mono fun _ hn ↦ hn.symm)
    convert h.div_const c using 1
    simp [hc]
  · intro h
    rw [LogAsymptotic] at h
    have hdiv : Tendsto (fun n ↦ (-Real.log (a n) / s n) / c)
        atTop (𝓝 1) := h.congr' heq
    have hmul := hdiv.mul_const c
    rw [HasNormalizedLogRate]
    simpa [hc] using hmul

/-- Perimeter scale. -/
def perimeterScale (n : ℕ) : ℝ := n

/-- Area scale. -/
def areaScale (n : ℕ) : ℝ := n ^ 2

theorem eventually_perimeterScale_ne_zero :
    ∀ᶠ n in atTop, perimeterScale n ≠ 0 := by
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
  unfold perimeterScale
  exact_mod_cast (show n ≠ 0 by omega)

theorem eventually_areaScale_ne_zero :
    ∀ᶠ n in atTop, areaScale n ≠ 0 := by
  filter_upwards [eventually_perimeterScale_ne_zero] with n hn
  simp [areaScale, perimeterScale] at hn ⊢
  exact hn

end Percolation
