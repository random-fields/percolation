import Percolation.Critical.SupercriticalFiniteRadiusRate
import Percolation.Critical.BoxFaces
import Percolation.Critical.RegionSymmetry

/-!
# Hyperplane reduction for positivity of the supercritical finite-radius rate

This file formalizes equation (8.43) and the final analytic implication in Grimmett's proof of
Theorem 8.21.  A finite origin cluster which reaches the boundary of `B(n)` reaches one of the
`2d` signed coordinate hyperplanes.  Consequently, a common exponential bound for those
hyperplane events forces the radius rate `a(p)` to be positive.

The remaining probabilistic input is the strip-exploration contraction (8.44)--(8.48), whose
construction uses the Grimmett--Marstrand slab approximation from Chapter 7.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators unitInterval

/-- Event `G_n` from the proof of Theorem 8.21, with an explicit signed coordinate direction:
the origin cluster is finite and reaches the corresponding coordinate hyperplane at distance
`n`. -/
def finiteClusterHitsSignedHyperplaneEvent (d n : ℕ) (a : CubicDirection d) :
    Set (EdgeConfiguration d) :=
  finiteClusterEvent d ∩
    ⋃ x : Cubic d,
      if x a.1 = (if a.2 then (n : ℤ) else -(n : ℤ)) then
        connectionEvent d cubicOrigin x
      else ∅

theorem measurableSet_finiteClusterHitsSignedHyperplaneEvent
    (d n : ℕ) (a : CubicDirection d) :
    MeasurableSet (finiteClusterHitsSignedHyperplaneEvent d n a) := by
  apply (measurableSet_finiteClusterEvent d).inter
  apply MeasurableSet.iUnion
  intro x
  by_cases hcoord : x a.1 = (if a.2 then (n : ℤ) else -(n : ℤ))
  · rw [if_pos hcoord]
    exact measurableSet_connectionEvent d cubicOrigin x
  · rw [if_neg hcoord]
    exact MeasurableSet.empty

theorem mem_finiteClusterHitsSignedHyperplaneEvent_iff
    {d n : ℕ} {a : CubicDirection d} {omega : EdgeConfiguration d} :
    omega ∈ finiteClusterHitsSignedHyperplaneEvent d n a ↔
      omega ∈ finiteClusterEvent d ∧
        ∃ x : Cubic d,
          x a.1 = (if a.2 then (n : ℤ) else -(n : ℤ)) ∧
            omega ∈ connectionEvent d cubicOrigin x := by
  simp only [finiteClusterHitsSignedHyperplaneEvent, Set.mem_inter_iff,
    Set.mem_iUnion]
  apply and_congr_right
  intro _hfinite
  constructor
  · rintro ⟨x, hx⟩
    by_cases hcoord : x a.1 = (if a.2 then (n : ℤ) else -(n : ℤ))
    · exact ⟨x, hcoord, by simpa [hcoord] using hx⟩
    · simp [hcoord] at hx
  · rintro ⟨x, hcoord, hconn⟩
    exact ⟨x, by simpa [hcoord] using hconn⟩

/-- At the origin, the finite-support surface event used in Chapter 7 is exactly the
coordinate-box radius event used in Chapter 6. -/
theorem connectionToBoxSurfaceEvent_origin_eq_boxRadiusConnectionEvent
    (d n : ℕ) :
    connectionToBoxSurfaceEvent d n cubicOrigin =
      boxRadiusConnectionEvent d cubicOrigin n := by
  ext omega
  rw [mem_boxRadiusConnectionEvent_iff_exists_connection]
  simp only [connectionToBoxSurfaceEvent, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hxSurface, hconn⟩
    exact ⟨x, hxSurface, connectionEventIn_subset d _ cubicOrigin x hconn⟩
  · rintro ⟨x, hxSurface, w, hwOpen⟩
    obtain ⟨z, hzSurface, hzConn⟩ :=
      exists_open_walk_to_cubicBoxSurface_in_box w hwOpen
        (mem_cubicBoxSurface.mp hxSurface).ge
    exact ⟨z, hzSurface, hzConn⟩

/-- Equation (8.43), event form: a finite cluster which reaches the box surface reaches one
of the `2d` signed coordinate hyperplanes. -/
theorem finiteBoxRadiusEvent_subset_iUnion_signedHyperplane
    {d n : ℕ} (hd : 0 < d) :
    finiteBoxRadiusEvent d n ⊆
      ⋃ a : CubicDirection d, finiteClusterHitsSignedHyperplaneEvent d n a := by
  intro omega homega
  have hradius : omega ∈ boxRadiusConnectionEvent d cubicOrigin n := by
    rw [← connectionToBoxSurfaceEvent_origin_eq_boxRadiusConnectionEvent]
    exact homega.1
  obtain ⟨i, hface⟩ := Set.mem_iUnion.mp
    (boxRadiusConnectionEvent_subset_iUnion_boxFaceConnectionEvent
      (d := d) (n := n) hd hradius)
  rcases hface with hpositive | hnegative
  · apply Set.mem_iUnion.mpr
    refine ⟨(i, true), ?_⟩
    rw [mem_finiteClusterHitsSignedHyperplaneEvent_iff]
    obtain ⟨x, hxFace, hxConn⟩ := hpositive
    refine ⟨homega.2, x, ?_, hxConn⟩
    simpa [cubicOrigin] using (mem_cubicBoxFace.mp hxFace).1
  · apply Set.mem_iUnion.mpr
    refine ⟨(i, false), ?_⟩
    rw [mem_finiteClusterHitsSignedHyperplaneEvent_iff]
    obtain ⟨x, hxFace, hxConn⟩ := hnegative
    refine ⟨homega.2, x, ?_, hxConn⟩
    simpa [cubicOrigin] using (mem_cubicBoxFace.mp hxFace).1

/-- Probability form of (8.43), before using symmetry: the finite-radius probability is at
most the sum of the `2d` signed-hyperplane probabilities. -/
theorem finiteBoxRadiusProbability_le_sum_signedHyperplane
    {d n : ℕ} (hd : 0 < d) (p : I) :
    finiteBoxRadiusProbability d p n ≤
      ∑ a : CubicDirection d,
        (bernoulliBondMeasure d p).real
          (finiteClusterHitsSignedHyperplaneEvent d n a) := by
  calc
    finiteBoxRadiusProbability d p n ≤
        (bernoulliBondMeasure d p).real
          (⋃ a : CubicDirection d,
            finiteClusterHitsSignedHyperplaneEvent d n a) :=
      measureReal_mono (finiteBoxRadiusEvent_subset_iUnion_signedHyperplane hd)
    _ ≤ ∑ a : CubicDirection d,
        (bernoulliBondMeasure d p).real
          (finiteClusterHitsSignedHyperplaneEvent d n a) :=
      measureReal_iUnion_fintype_le _

/-- Symmetry transport for signed-hyperplane events under an origin-fixing cubic graph
automorphism. -/
theorem finiteClusterHitsSignedHyperplane_probability_eq_of_iso
    {d n : ℕ} (p : I) (a b : CubicDirection d)
    (F : cubicGraph d ≃g cubicGraph d)
    (hF0 : F cubicOrigin = cubicOrigin)
    (hcoord : ∀ x : Cubic d,
      x a.1 = (if a.2 then (n : ℤ) else -(n : ℤ)) →
        F x b.1 = (if b.2 then (n : ℤ) else -(n : ℤ)))
    (hcoordBack : ∀ y : Cubic d,
      y b.1 = (if b.2 then (n : ℤ) else -(n : ℤ)) →
        F.symm y a.1 = (if a.2 then (n : ℤ) else -(n : ℤ))) :
    (bernoulliBondMeasure d p).real
        (finiteClusterHitsSignedHyperplaneEvent d n a) =
      (bernoulliBondMeasure d p).real
        (finiteClusterHitsSignedHyperplaneEvent d n b) := by
  let T := cubicGraphIsoConfigurationPullback F
  have hfinite (omega : EdgeConfiguration d) :
      T omega ∈ finiteClusterEvent d ↔ omega ∈ finiteClusterEvent d := by
    rw [finiteClusterEvent_eq_compl_infinite]
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    apply not_congr
    rw [← hasInfiniteOpenClusterFrom_origin,
      ← hasInfiniteOpenClusterFrom_origin]
    simpa only [T, hF0] using
      (cubicGraphIsoConfigurationPullback_hasInfiniteOpenClusterFrom_iff
        F omega cubicOrigin)
  have hpre : T ⁻¹' finiteClusterHitsSignedHyperplaneEvent d n a =
      finiteClusterHitsSignedHyperplaneEvent d n b := by
    ext omega
    rw [Set.mem_preimage, mem_finiteClusterHitsSignedHyperplaneEvent_iff,
      mem_finiteClusterHitsSignedHyperplaneEvent_iff, hfinite]
    apply and_congr_right
    intro _hfinite
    constructor
    · rintro ⟨x, hxcoord, hxconn⟩
      refine ⟨F x, hcoord x hxcoord, ?_⟩
      have hmap :=
        (cubicGraphIsoConfigurationPullback_mem_connectionEvent_iff
          F omega cubicOrigin x).mp hxconn
      simpa only [hF0] using hmap
    · rintro ⟨y, hycoord, hyconn⟩
      refine ⟨F.symm y, hcoordBack y hycoord, ?_⟩
      apply (cubicGraphIsoConfigurationPullback_mem_connectionEvent_iff
        F omega cubicOrigin (F.symm y)).mpr
      simpa [hF0] using hyconn
  have hmap := congrArg
    (fun mu : Measure (EdgeConfiguration d) ↦
      mu (finiteClusterHitsSignedHyperplaneEvent d n a))
    (bernoulliBondMeasure_map_cubicGraphIsoConfigurationPullback p F)
  change (Measure.map T (bernoulliBondMeasure d p))
      (finiteClusterHitsSignedHyperplaneEvent d n a) =
    (bernoulliBondMeasure d p)
      (finiteClusterHitsSignedHyperplaneEvent d n a) at hmap
  rw [Measure.map_apply (measurable_cubicGraphIsoConfigurationPullback F)
    (measurableSet_finiteClusterHitsSignedHyperplaneEvent d n a), hpre] at hmap
  exact (congrArg ENNReal.toReal hmap).symm

/-- Coordinate permutations carry a signed-hyperplane probability from coordinate `i` to
coordinate `e i`. -/
theorem finiteClusterHitsSignedHyperplane_probability_permutation
    {d n : ℕ} (p : I) (e : Fin d ≃ Fin d) (i : Fin d) (positive : Bool) :
    (bernoulliBondMeasure d p).real
        (finiteClusterHitsSignedHyperplaneEvent d n (i, positive)) =
      (bernoulliBondMeasure d p).real
        (finiteClusterHitsSignedHyperplaneEvent d n (e i, positive)) := by
  let F := cubicCoordinatePermutationIso e
  apply finiteClusterHitsSignedHyperplane_probability_eq_of_iso
    p (i, positive) (e i, positive) F
  · ext j
    simp [F, cubicCoordinatePermutationIso,
      cubicCoordinatePermutationEquiv, cubicOrigin]
  · intro x hx
    simpa [F, cubicCoordinatePermutationIso,
      cubicCoordinatePermutationEquiv] using hx
  · intro y hy
    simpa [F, cubicCoordinatePermutationIso,
      cubicCoordinatePermutationEquiv] using hy

/-- Reflection in coordinate `i` identifies the two signs of the hyperplane event. -/
theorem finiteClusterHitsSignedHyperplane_probability_true_eq_false
    {d n : ℕ} (p : I) (i : Fin d) :
    (bernoulliBondMeasure d p).real
        (finiteClusterHitsSignedHyperplaneEvent d n (i, true)) =
      (bernoulliBondMeasure d p).real
        (finiteClusterHitsSignedHyperplaneEvent d n (i, false)) := by
  let F := cubicCoordinateReflectionIso i
  apply finiteClusterHitsSignedHyperplane_probability_eq_of_iso
    p (i, true) (i, false) F
  · ext j
    simp [F, cubicCoordinateReflectionIso,
      cubicCoordinateReflectionEquiv, cubicOrigin]
  · intro x hx
    simpa [F, cubicCoordinateReflectionIso,
      cubicCoordinateReflectionEquiv] using congrArg Neg.neg hx
  · intro y hy
    simpa [F, cubicCoordinateReflectionIso,
      cubicCoordinateReflectionEquiv] using congrArg Neg.neg hy

/-- Grimmett's reference event `G_n`: the finite origin cluster reaches the positive first
coordinate hyperplane. -/
def finiteClusterHitsHyperplaneEvent (d : ℕ) (hd : 0 < d) (n : ℕ) :
    Set (EdgeConfiguration d) :=
  finiteClusterHitsSignedHyperplaneEvent d n (⟨0, hd⟩, true)

theorem finiteClusterHitsSignedHyperplane_probability_eq_reference
    {d n : ℕ} (hd : 0 < d) (p : I) (a : CubicDirection d) :
    (bernoulliBondMeasure d p).real
        (finiteClusterHitsSignedHyperplaneEvent d n a) =
      (bernoulliBondMeasure d p).real
        (finiteClusterHitsHyperplaneEvent d hd n) := by
  rcases a with ⟨i, positive⟩
  let i0 : Fin d := ⟨0, hd⟩
  cases positive with
  | false =>
      rw [← finiteClusterHitsSignedHyperplane_probability_true_eq_false p i]
      have hperm := finiteClusterHitsSignedHyperplane_probability_permutation
        (n := n) p (Equiv.swap i i0) i true
      rw [Equiv.swap_apply_left] at hperm
      simpa only [finiteClusterHitsHyperplaneEvent, i0] using hperm
  | true =>
      have hperm := finiteClusterHitsSignedHyperplane_probability_permutation
        (n := n) p (Equiv.swap i i0) i true
      rw [Equiv.swap_apply_left] at hperm
      simpa only [finiteClusterHitsHyperplaneEvent, i0] using hperm

/-- Exact source-facing equation (8.43): by signed-coordinate symmetry, the finite-radius
probability is at most `2d` times the probability of the single reference event `G_n`. -/
theorem finiteBoxRadiusProbability_le_two_mul_d_mul_finiteClusterHitsHyperplaneProbability
    {d n : ℕ} (hd : 0 < d) (p : I) :
    finiteBoxRadiusProbability d p n ≤
      (2 * d : ℝ) *
        (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d hd n) := by
  calc
    finiteBoxRadiusProbability d p n ≤
        ∑ a : CubicDirection d,
          (bernoulliBondMeasure d p).real
            (finiteClusterHitsSignedHyperplaneEvent d n a) :=
      finiteBoxRadiusProbability_le_sum_signedHyperplane hd p
    _ = ∑ _a : CubicDirection d,
        (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d hd n) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact finiteClusterHitsSignedHyperplane_probability_eq_reference hd p a
    _ = (2 * d : ℝ) *
        (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d hd n) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [CubicDirection, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, nsmul_eq_mul]
      push_cast
      ring

/-- If every signed-hyperplane event has the same exponential upper bound, equation (8.43)
gives the source prefactor `2d` for the finite-radius event. -/
theorem finiteBoxRadiusProbability_le_two_mul_d_mul_exp_of_signedHyperplane_bound
    {d n : ℕ} (hd : 0 < d) (p : I) {gamma : ℝ}
    (hbound : ∀ a : CubicDirection d,
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsSignedHyperplaneEvent d n a) ≤
        Real.exp (-((n : ℝ) * gamma))) :
    finiteBoxRadiusProbability d p n ≤
      (2 * d : ℝ) * Real.exp (-((n : ℝ) * gamma)) := by
  calc
    finiteBoxRadiusProbability d p n ≤
        ∑ a : CubicDirection d,
          (bernoulliBondMeasure d p).real
            (finiteClusterHitsSignedHyperplaneEvent d n a) :=
      finiteBoxRadiusProbability_le_sum_signedHyperplane hd p
    _ ≤ ∑ _a : CubicDirection d, Real.exp (-((n : ℝ) * gamma)) := by
      exact Finset.sum_le_sum fun a _ha ↦ hbound a
    _ = (2 * d : ℝ) * Real.exp (-((n : ℝ) * gamma)) := by
      simp [CubicDirection]
      ring

/-- Analytic final step of Theorem 8.21: an exponential signed-hyperplane estimate implies
that the limiting radius rate is at least its exponent. -/
theorem gamma_le_finiteClusterRadiusDecayRate_of_signedHyperplane_bound
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {gamma : ℝ}
    (hbound : ∀ n : ℕ, ∀ a : CubicDirection d,
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsSignedHyperplaneEvent d n a) ≤
        Real.exp (-((n : ℝ) * gamma))) :
    gamma ≤ finiteClusterRadiusDecayRate d p := by
  let C : ℝ := 2 * d
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlower : Tendsto
      (fun n : ℕ ↦ gamma - Real.log C / (n : ℝ)) atTop (nhds gamma) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  have hrate := finiteBoxRadiusProbability_logRate_tendsto hd p hp0 hp1
  have hle : ∀ᶠ n : ℕ in atTop,
      gamma - Real.log C / (n : ℝ) ≤
        -Real.log (finiteBoxRadiusProbability d p n) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hR : 0 < finiteBoxRadiusProbability d p n :=
      finiteBoxRadiusProbability_pos hd p hp0 hp1 n
    have hboundR : finiteBoxRadiusProbability d p n ≤
        C * Real.exp (-((n : ℝ) * gamma)) := by
      simpa only [C] using
        finiteBoxRadiusProbability_le_two_mul_d_mul_exp_of_signedHyperplane_bound
          (Nat.zero_lt_of_lt hd) p (hbound n)
    have hright : 0 < C * Real.exp (-((n : ℝ) * gamma)) :=
      mul_pos hC (Real.exp_pos _)
    have hlog := Real.log_le_log hR hboundR
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hnreal : (0 : ℝ) < n := by positivity
    rw [le_div_iff₀ hnreal]
    field_simp
    nlinarith
  exact le_of_tendsto_of_tendsto hlower hrate hle

/-- Positive-exponent form of the preceding theorem, matching the conclusion `a(p)>0` in
Theorem 8.21. -/
theorem finiteClusterRadiusDecayRate_pos_of_signedHyperplane_bound
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {gamma : ℝ} (hgamma : 0 < gamma)
    (hbound : ∀ n : ℕ, ∀ a : CubicDirection d,
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsSignedHyperplaneEvent d n a) ≤
        Real.exp (-((n : ℝ) * gamma))) :
    0 < finiteClusterRadiusDecayRate d p :=
  hgamma.trans_le
    (gamma_le_finiteClusterRadiusDecayRate_of_signedHyperplane_bound
      hd p hp0 hp1 hbound)

/-- Source-facing version of the exponential reduction: it is enough to bound Grimmett's one
reference event `G_n`, since all `2d` signed events have the same probability. -/
theorem finiteBoxRadiusProbability_le_two_mul_d_mul_exp_of_hyperplane_bound
    {d n : ℕ} (hd : 0 < d) (p : I) {gamma : ℝ}
    (hbound :
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d hd n) ≤
        Real.exp (-((n : ℝ) * gamma))) :
    finiteBoxRadiusProbability d p n ≤
      (2 * d : ℝ) * Real.exp (-((n : ℝ) * gamma)) := by
  exact (finiteBoxRadiusProbability_le_two_mul_d_mul_finiteClusterHitsHyperplaneProbability
    hd p).trans (mul_le_mul_of_nonneg_left hbound (by positivity))

/-- Exact analytic conclusion used after (8.44): the decay exponent for `G_n` is a lower
bound for `a(p)`. -/
theorem gamma_le_finiteClusterRadiusDecayRate_of_hyperplane_bound
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {gamma : ℝ}
    (hbound : ∀ n : ℕ,
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d (Nat.zero_lt_of_lt hd) n) ≤
        Real.exp (-((n : ℝ) * gamma))) :
    gamma ≤ finiteClusterRadiusDecayRate d p := by
  apply gamma_le_finiteClusterRadiusDecayRate_of_signedHyperplane_bound
    hd p hp0 hp1
  intro n a
  rw [finiteClusterHitsSignedHyperplane_probability_eq_reference
    (Nat.zero_lt_of_lt hd) p a]
  exact hbound n

/-- Positive-exponent source form of Theorem 8.21's final step. -/
theorem finiteClusterRadiusDecayRate_pos_of_hyperplane_bound
    {d : ℕ} (hd : 2 ≤ d) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {gamma : ℝ} (hgamma : 0 < gamma)
    (hbound : ∀ n : ℕ,
      (bernoulliBondMeasure d p).real
          (finiteClusterHitsHyperplaneEvent d (Nat.zero_lt_of_lt hd) n) ≤
        Real.exp (-((n : ℝ) * gamma))) :
    0 < finiteClusterRadiusDecayRate d p :=
  hgamma.trans_le
    (gamma_le_finiteClusterRadiusDecayRate_of_hyperplane_bound
      hd p hp0 hp1 hbound)

end Percolation
