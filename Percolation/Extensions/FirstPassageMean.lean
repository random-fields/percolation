import Percolation.Extensions.FirstPassageProbability
import Mathlib.Analysis.Subadditive

/-!
# Mean axial first-passage times

This file supplies the deterministic-expectation layer preceding the subadditive ergodic
theorem in Grimmett, Chapter 12, section 12.9.  Under a finite first moment for the one-edge
law, axial passage times have finite mean, their means are subadditive, and Fekete's lemma
gives the mean time constant.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- A fixed shortest walk from the origin to `n e₁`. -/
noncomputable def firstPassageAxisWalk
    (d : ℕ) (n : ℕ) :
    (cubicGraph d).Walk cubicOrigin (cubicAxisVertex d n) :=
  Classical.choose (exists_cubicWalk_length_eq_l1Dist
    d cubicOrigin (cubicAxisVertex d n))

@[simp]
theorem firstPassageAxisWalk_length
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (firstPassageAxisWalk d n).length = n := by
  rw [show (firstPassageAxisWalk d n).length =
      cubicL1Dist cubicOrigin (cubicAxisVertex d n) from
    Classical.choose_spec (exists_cubicWalk_length_eq_l1Dist
      d cubicOrigin (cubicAxisVertex d n))]
  exact cubicL1Dist_origin_axisVertex hd

/-- Extended first moment of the one-edge passage-time law. -/
noncomputable def firstPassageEdgeMean (ν : Measure ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ r, r ∂ν

/-- Every edge coordinate under the iid environment has the prescribed one-edge mean. -/
theorem lintegral_firstPassageEdgeWeight_eq_edgeMean
    {d : ℕ} (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    {e : Sym2 (Cubic d)} (he : e ∈ (cubicGraph d).edgeSet) :
    (∫⁻ t, firstPassageEdgeWeight t e ∂firstPassageMeasure ν) =
      firstPassageEdgeMean ν := by
  rw [show (fun t : FirstPassageConfiguration d ↦ firstPassageEdgeWeight t e) =
      fun t ↦ t (⟨e, he⟩ : CubicEdge d) by
    funext t
    simp [firstPassageEdgeWeight, he]]
  unfold firstPassageEdgeMean firstPassageMeasure
  calc
    (∫⁻ t : FirstPassageConfiguration d, t (⟨e, he⟩ : CubicEdge d)
        ∂Measure.infinitePi fun _ : CubicEdge d ↦ ν) =
        ∫⁻ r : ℝ≥0∞, r ∂Measure.map
          (fun t : FirstPassageConfiguration d ↦ t (⟨e, he⟩ : CubicEdge d))
          (Measure.infinitePi fun _ : CubicEdge d ↦ ν) :=
      (MeasureTheory.lintegral_map (measurable_id : Measurable fun r : ℝ≥0∞ ↦ r)
        (measurable_pi_apply (⟨e, he⟩ : CubicEdge d))).symm
    _ = ∫⁻ r : ℝ≥0∞, r ∂ν := by rw [Measure.infinitePi_map_eval]

private theorem lintegral_firstPassageListTime_eq
    {d : ℕ} (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (l : List (Sym2 (Cubic d)))
    (hl : ∀ e ∈ l, e ∈ (cubicGraph d).edgeSet) :
    (∫⁻ t, (l.map (firstPassageEdgeWeight t)).sum
      ∂firstPassageMeasure ν) =
      (l.length : ℝ≥0∞) * firstPassageEdgeMean ν := by
  induction l with
  | nil => simp
  | cons e l ih =>
      have he : e ∈ (cubicGraph d).edgeSet := hl e (by simp)
      have htail : ∀ q ∈ l, q ∈ (cubicGraph d).edgeSet := by
        intro q hq
        exact hl q (by simp [hq])
      simp only [List.map_cons, List.sum_cons]
      rw [MeasureTheory.lintegral_add_left
        (measurable_firstPassageEdgeWeight e) _,
        lintegral_firstPassageEdgeWeight_eq_edgeMean ν he,
        ih htail]
      rw [List.length_cons, Nat.cast_succ, add_mul, one_mul]
      ac_rfl

/-- The expected time of any fixed lattice walk is its length times the one-edge mean. -/
theorem lintegral_firstPassagePathTime_eq_length_mul_edgeMean
    {d : ℕ} (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    {x y : Cubic d} (w : (cubicGraph d).Walk x y) :
    (∫⁻ t, firstPassagePathTime t w ∂firstPassageMeasure ν) =
      (w.length : ℝ≥0∞) * firstPassageEdgeMean ν := by
  unfold firstPassagePathTime
  have h := lintegral_firstPassageListTime_eq (d := d) ν w.edges
    (fun e he ↦ w.edges_subset_edgeSet he)
  simpa only [w.length_edges] using h

/-- Extended mean passage time from the origin to `n e₁`. -/
noncomputable def meanAxialFirstPassageTime
    {d : ℕ} (ν : Measure ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ t, axialFirstPassageTime t n ∂firstPassageMeasure (d := d) ν

theorem meanAxialFirstPassageTime_le
    {d : ℕ} (hd : 0 < d) (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (n : ℕ) :
    meanAxialFirstPassageTime (d := d) ν n ≤
      (n : ℝ≥0∞) * firstPassageEdgeMean ν := by
  calc
    meanAxialFirstPassageTime (d := d) ν n ≤
        ∫⁻ t, firstPassagePathTime t (firstPassageAxisWalk d n)
          ∂firstPassageMeasure (d := d) ν :=
      lintegral_mono fun t ↦ firstPassageTime_le_pathTime t _
    _ = (n : ℝ≥0∞) * firstPassageEdgeMean ν := by
      rw [lintegral_firstPassagePathTime_eq_length_mul_edgeMean,
        firstPassageAxisWalk_length d hd n]

@[simp]
theorem axialFirstPassageTime_eq_axialPassageTime_zero
    {d : ℕ} (t : FirstPassageConfiguration d) (n : ℕ) :
    axialFirstPassageTime t n = axialPassageTime t 0 n := by
  unfold axialFirstPassageTime axialPassageTime
  congr 2
  ext i
  simp [cubicOrigin, cubicAxisVertex]

private theorem lintegral_axialPassageTime_shift_eq
    {d : ℕ} (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (k m n : ℕ) :
    (∫⁻ t, axialPassageTime t (k + m) (k + n)
      ∂firstPassageMeasure (d := d) ν) =
      ∫⁻ t : FirstPassageConfiguration d, axialPassageTime t m n
        ∂firstPassageMeasure (d := d) ν := by
  have hLaw := axialPassageTime_stationary (d := d) ν k m n
  calc
    (∫⁻ t, axialPassageTime t (k + m) (k + n)
        ∂firstPassageMeasure ν) =
        ∫⁻ r, r ∂Measure.map
          (fun t : FirstPassageConfiguration d ↦
            axialPassageTime t (k + m) (k + n))
          (firstPassageMeasure (d := d) ν) :=
      (MeasureTheory.lintegral_map measurable_id
        (measurable_axialPassageTime (k + m) (k + n))).symm
    _ = ∫⁻ r, r ∂Measure.map
          (fun t : FirstPassageConfiguration d ↦ axialPassageTime t m n)
          (firstPassageMeasure (d := d) ν) := by rw [hLaw]
    _ = ∫⁻ t : FirstPassageConfiguration d, axialPassageTime t m n
          ∂firstPassageMeasure (d := d) ν :=
      MeasureTheory.lintegral_map measurable_id
        (measurable_axialPassageTime m n)

/-- Stationarity plus the pathwise triangle inequality makes the extended mean axial passage
time subadditive. -/
theorem meanAxialFirstPassageTime_subadditive
    {d : ℕ} (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν] :
    ∀ m n : ℕ,
      meanAxialFirstPassageTime (d := d) ν (m + n) ≤
        meanAxialFirstPassageTime (d := d) ν m +
          meanAxialFirstPassageTime (d := d) ν n := by
  intro m n
  simp only [meanAxialFirstPassageTime,
    axialFirstPassageTime_eq_axialPassageTime_zero]
  calc
    (∫⁻ t : FirstPassageConfiguration d, axialPassageTime t 0 (m + n)
        ∂firstPassageMeasure (d := d) ν) ≤
        ∫⁻ t, axialPassageTime t 0 m + axialPassageTime t m (m + n)
          ∂firstPassageMeasure (d := d) ν :=
      lintegral_mono fun t ↦ axialPassageTime_subadditive t 0 m (m + n)
    _ = (∫⁻ t : FirstPassageConfiguration d, axialPassageTime t 0 m
          ∂firstPassageMeasure (d := d) ν) +
        ∫⁻ t : FirstPassageConfiguration d, axialPassageTime t m (m + n)
          ∂firstPassageMeasure (d := d) ν := by
      rw [MeasureTheory.lintegral_add_left
        (measurable_axialPassageTime 0 m) _]
    _ = (∫⁻ t : FirstPassageConfiguration d, axialPassageTime t 0 m
          ∂firstPassageMeasure (d := d) ν) +
        ∫⁻ t : FirstPassageConfiguration d, axialPassageTime t 0 n
          ∂firstPassageMeasure (d := d) ν := by
      congr 1
      simpa using (lintegral_axialPassageTime_shift_eq (d := d) ν m 0 n)

/-- Real mean passage time.  Its use is paired with the finite-one-edge-mean hypothesis, so
the totalized value of `ENNReal.toReal` at infinity never enters a source-facing theorem. -/
noncomputable def meanAxialFirstPassageTimeReal
    {d : ℕ} (ν : Measure ℝ≥0∞) (n : ℕ) : ℝ :=
  (meanAxialFirstPassageTime (d := d) ν n).toReal

theorem meanAxialFirstPassageTime_ne_top
    {d : ℕ} (hd : 0 < d) (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (hmean : firstPassageEdgeMean ν < ⊤) (n : ℕ) :
    meanAxialFirstPassageTime (d := d) ν n ≠ ⊤ := by
  apply ne_of_lt
  exact (meanAxialFirstPassageTime_le hd ν n).trans_lt (ENNReal.mul_lt_top
    (ENNReal.natCast_lt_top n) hmean)

/-- Subadditivity of the real mean sequence under the finite first-moment hypothesis. -/
theorem meanAxialFirstPassageTimeReal_subadditive
    {d : ℕ} (hd : 0 < d) (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (hmean : firstPassageEdgeMean ν < ⊤) :
    Subadditive (meanAxialFirstPassageTimeReal (d := d) ν) := by
  intro m n
  have hsub := meanAxialFirstPassageTime_subadditive (d := d) ν m n
  have hm := meanAxialFirstPassageTime_ne_top hd ν hmean m
  have hn := meanAxialFirstPassageTime_ne_top hd ν hmean n
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hm, hn⟩) hsub).trans_eq
    (ENNReal.toReal_add hm hn)

/-- The normalized real mean axial passage times are bounded below by zero. -/
theorem meanAxialFirstPassageTimeReal_div_bddBelow
    {d : ℕ} (ν : Measure ℝ≥0∞) :
    BddBelow (range fun n : ℕ ↦
      meanAxialFirstPassageTimeReal (d := d) ν n / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg n)

/-- Mean time constant obtained from Fekete's lemma. -/
noncomputable def firstPassageMeanTimeConstant
    {d : ℕ} (hd : 0 < d) (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (hmean : firstPassageEdgeMean ν < ⊤) : ℝ :=
  (meanAxialFirstPassageTimeReal_subadditive hd ν hmean).lim

/-- Fekete limit for expected axial passage time.  This is the expectation-level precursor of
the almost-sure time-constant theorem stated in section 12.9. -/
theorem meanAxialFirstPassageTime_div_tendsto
    {d : ℕ} (hd : 0 < d) (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν]
    (hmean : firstPassageEdgeMean ν < ⊤) :
    Tendsto (fun n : ℕ ↦ meanAxialFirstPassageTimeReal (d := d) ν n / n)
      atTop (nhds (firstPassageMeanTimeConstant hd ν hmean)) :=
  (meanAxialFirstPassageTimeReal_subadditive hd ν hmean).tendsto_lim
    (meanAxialFirstPassageTimeReal_div_bddBelow ν)

end Percolation
