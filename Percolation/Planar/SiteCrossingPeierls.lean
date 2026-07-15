import Percolation.Planar.SiteCrossingInterface
import Percolation.Bernoulli.Basic

/-!
# Peierls count for closed star paths

This file proves the probability-counting half of Grimmett (7.70). A self-avoiding length-`n`
star path has `n+1` distinct sites, so a fixed code is closed with probability `(1-p)^(n+1)`.
There are at most `8^n` codes from a fixed start.

The separate planar frontier file constructs a closed separator when a left-right site crossing
fails, and the interface file extracts a top-bottom star path from that separator.  The results
below combine that deterministic alternative with the degree-eight count to prove the full
high-density site-crossing estimate.
-/

namespace Percolation

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

/-- Some self-avoiding star walk of length `n` from `x` has all its sites closed. -/
def closedSquareStarSelfAvoidingWalkEvent
    (x : SquareVertex) (n : ℕ) : Set (Set SquareVertex) :=
  ⋃ c : SquareStarSelfAvoidingCode x n,
    {eta : Set SquareVertex |
      Disjoint
        ((squareStarWalkFromVector x c.1).2.support.toFinset : Set SquareVertex) eta}

theorem measurableSet_closedSquareStarSelfAvoidingWalkEvent
    (x : SquareVertex) (n : ℕ) :
    MeasurableSet (closedSquareStarSelfAvoidingWalkEvent x n) := by
  apply MeasurableSet.iUnion
  intro c
  exact measurableSet_disjoint_finset _

/-- Fixed-start degree-eight Peierls bound for closed star paths. -/
theorem setBernoulli_real_closedSquareStarSelfAvoidingWalkEvent_le
    (p : I) (x : SquareVertex) (n : ℕ) :
    setBer((Set.univ : Set SquareVertex), p).real
        (closedSquareStarSelfAvoidingWalkEvent x n) ≤
      (8 : ℝ) ^ n * (1 - (p : ℝ)) ^ (n + 1) := by
  classical
  calc
    setBer((Set.univ : Set SquareVertex), p).real
        (closedSquareStarSelfAvoidingWalkEvent x n) ≤
        ∑ c : SquareStarSelfAvoidingCode x n,
          setBer((Set.univ : Set SquareVertex), p).real
            {eta : Set SquareVertex |
              Disjoint
                ((squareStarWalkFromVector x c.1).2.support.toFinset : Set SquareVertex) eta} :=
      measureReal_iUnion_fintype_le _
    _ = Fintype.card (SquareStarSelfAvoidingCode x n) *
        (1 - (p : ℝ)) ^ (n + 1) := by
      have hcard (c : SquareStarSelfAvoidingCode x n) :
          (squareStarWalkFromVector x c.1).2.support.toFinset.card = n + 1 := by
        rw [List.toFinset_card_of_nodup c.2.support_nodup,
          SimpleGraph.Walk.length_support, squareStarWalkFromVector_length]
      simp_rw [setBernoulli_real_disjoint_finset_univ, hcard]
      simp
    _ ≤ (8 : ℝ) ^ n * (1 - (p : ℝ)) ^ (n + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_squareStarSelfAvoidingCode_le x n
      · exact pow_nonneg (sub_nonneg.mpr p.2.2) _

/-- A star walk's vertical displacement is at most its length. -/
theorem squareStarWalk_verticalDist_le_length {x y : SquareVertex}
    (w : squareStarGraph.Walk x y) :
    (y 1 - x 1).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons x y z hxy p ih =>
      have hxyCoord : (y 1 - x 1).natAbs ≤ 1 :=
        (cubicLInfDist_coord_le x y (1 : Fin 2)).trans hxy.2
      calc
        (z 1 - x 1).natAbs ≤
            (y 1 - x 1).natAbs + (z 1 - y 1).natAbs := by
          have h := Int.natAbs_add_le (y 1 - x 1) (z 1 - y 1)
          convert h using 1 <;> omega
        _ ≤ 1 + p.length := Nat.add_le_add hxyCoord ih
        _ = (SimpleGraph.Walk.cons hxy p).length := by simp [Nat.add_comm]

/-- A bottom-to-top star walk across `[0,m] × [-n,n]` has at least `2n` edges. -/
theorem two_mul_le_length_of_squareStarWalk_bottom_top
    {n : ℕ} {x y : SquareVertex} (hx : x 1 = -(n : ℤ))
    (hy : y 1 = (n : ℤ)) (w : squareStarGraph.Walk x y) :
    2 * n ≤ w.length := by
  have h := squareStarWalk_verticalDist_le_length w
  rw [hx, hy] at h
  have heq : (n : ℤ) - (-(n : ℤ)) = ((n + n : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq, Int.natAbs_natCast] at h
  simpa [two_mul] using h

/-- A closed self-avoiding star walk witnesses the corresponding fixed-start event. -/
theorem mem_closedSquareStarSelfAvoidingWalkEvent_of_walk
    {eta : Set SquareVertex} {x y : SquareVertex}
    {n : ℕ} (w : squareStarGraph.Walk x y)
    (hwPath : w.IsPath) (hwLength : w.length = n)
    (hwClosed : ∀ z ∈ w.support, z ∉ eta) :
    eta ∈ closedSquareStarSelfAvoidingWalkEvent x n := by
  subst hwLength
  let c := squareStarSelfAvoidingCodeOfWalk w hwPath
  rw [closedSquareStarSelfAvoidingWalkEvent, Set.mem_iUnion]
  refine ⟨c, ?_⟩
  have hsupport : (squareStarWalkFromVector x c.1).2.support = w.support := by
    have h := squareStarWalkFromVector_code w
    exact congrArg (fun q : Σ y, squareStarGraph.Walk x y ↦ q.2.support) h
  rw [hsupport]
  change Disjoint (w.support.toFinset : Set SquareVertex) eta
  rw [Set.disjoint_left]
  intro z hz hzo
  exact hwClosed z (by simpa using hz) hzo

/-- The bottom side of the site rectangle. -/
noncomputable def squareRectangleBottom (m n : ℕ) : Finset SquareVertex :=
  (squareRectangleVertices m n).filter fun x ↦ x 1 = -(n : ℤ)

@[simp]
theorem mem_squareRectangleBottom_iff {m n : ℕ} {x : SquareVertex} :
    x ∈ squareRectangleBottom m n ↔
      0 ≤ x 0 ∧ x 0 ≤ (m : ℤ) ∧ x 1 = -(n : ℤ) := by
  classical
  simp only [squareRectangleBottom, Finset.mem_filter, mem_squareRectangleVertices_iff]
  omega

@[simp]
theorem card_squareRectangleBottom (m n : ℕ) :
    (squareRectangleBottom m n).card = m + 1 := by
  classical
  let f : Fin (m + 1) ↪ SquareVertex :=
    { toFun := fun j ↦ squareVertex (j : ℤ) (-(n : ℤ))
      inj' := by
        intro j k h
        apply Fin.ext
        have hcoord := congrFun h (0 : Fin 2)
        simpa [squareVertex] using hcoord }
  have hbottom : squareRectangleBottom m n = Finset.univ.map f := by
    ext x
    rw [mem_squareRectangleBottom_iff, Finset.mem_map]
    constructor
    · rintro ⟨hx0, hxm, hx1⟩
      let j : Fin (m + 1) :=
        ⟨x 0 |>.toNat, by
          rw [← Int.ofNat_lt]
          rw [Int.toNat_of_nonneg hx0]
          omega⟩
      refine ⟨j, Finset.mem_univ _, ?_⟩
      ext i
      fin_cases i
      · simp [f, j, squareVertex, Int.toNat_of_nonneg hx0]
      · simpa [f, squareVertex] using hx1.symm
    · rintro ⟨j, _hj, rfl⟩
      simp [f, squareVertex]
      omega
  rw [hbottom, Finset.card_map]
  simp

/-- Failure of a left-right crossing is covered by fixed-start closed star-path events.

The separator may be longer than the rectangle height.  Taking its first `2 * n` edges gives
the fixed-length witness needed by the Peierls count. -/
theorem compl_siteSquareRectangleCrossingEvent_subset_closedSquareStarWalk_union
    {m n : ℕ} (hn : 0 < n) :
    (siteSquareRectangleCrossingEvent m n)ᶜ ⊆
      ⋃ x ∈ squareRectangleBottom m n,
        closedSquareStarSelfAvoidingWalkEvent x (2 * n) := by
  intro eta heta
  have hno : eta ∉ siteSquareRectangleCrossingEvent m n := by
    simpa only [Set.mem_compl_iff] using heta
  rcases exists_closed_squareStar_path_bottom_top_of_not_crossing hn hno with
    ⟨x, y, hxRect, hxRow, _hyRect, hyRow, w, hwPath, _hwBoundary, hwClosed⟩
  have hlength : 2 * n ≤ w.length :=
    two_mul_le_length_of_squareStarWalk_bottom_top hxRow hyRow w
  have hxBottom : x ∈ squareRectangleBottom m n := by
    rw [mem_squareRectangleBottom_iff]
    exact ⟨(mem_squareRectangleVertices_iff.mp hxRect).1,
      (mem_squareRectangleVertices_iff.mp hxRect).2.1, hxRow⟩
  rw [Set.mem_iUnion]
  refine ⟨x, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hxBottom, ?_⟩
  apply mem_closedSquareStarSelfAvoidingWalkEvent_of_walk (w.take (2 * n))
  · exact hwPath.take _
  · rw [w.take_length, min_eq_left hlength]
  · intro z hz
    exact hwClosed z ((SimpleGraph.Walk.isSubwalk_take w (2 * n)).support_subset hz)

/-- Explicit Peierls bound for failure of an open-site rectangle crossing. -/
theorem setBernoulli_real_compl_siteSquareRectangleCrossingEvent_le
    (p : I) (m n : ℕ) (hn : 0 < n) :
    setBer((Set.univ : Set SquareVertex), p).real
        (siteSquareRectangleCrossingEvent m n)ᶜ ≤
      ((m + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (2 * n) *
        (1 - (p : ℝ)) ^ (2 * n + 1) := by
  let μ := setBer((Set.univ : Set SquareVertex), p)
  calc
    μ.real (siteSquareRectangleCrossingEvent m n)ᶜ ≤
        μ.real (⋃ x ∈ squareRectangleBottom m n,
          closedSquareStarSelfAvoidingWalkEvent x (2 * n)) :=
      measureReal_mono
        (compl_siteSquareRectangleCrossingEvent_subset_closedSquareStarWalk_union hn)
        (measure_ne_top _ _)
    _ ≤ ∑ x ∈ squareRectangleBottom m n,
        μ.real (closedSquareStarSelfAvoidingWalkEvent x (2 * n)) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ squareRectangleBottom m n,
        (8 : ℝ) ^ (2 * n) * (1 - (p : ℝ)) ^ (2 * n + 1) := by
      apply Finset.sum_le_sum
      intro x _hx
      exact setBernoulli_real_closedSquareStarSelfAvoidingWalkEvent_le p x (2 * n)
    _ = ((m + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (2 * n) *
        (1 - (p : ℝ)) ^ (2 * n + 1) := by
      rw [Finset.sum_const, card_squareRectangleBottom]
      push_cast
      simp [nsmul_eq_mul]
      ring

/-- Equation (7.70), quantitative form: the crossing failure probability has the explicit
closed-star Peierls upper bound. -/
theorem one_sub_siteSquareRectangleCrossingProbability_le
    (p : I) (m n : ℕ) (hn : 0 < n) :
    1 - siteSquareRectangleCrossingProbability p m n ≤
      ((m + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (2 * n) *
        (1 - (p : ℝ)) ^ (2 * n + 1) := by
  have h := setBernoulli_real_compl_siteSquareRectangleCrossingEvent_le p m n hn
  simpa only [siteSquareRectangleCrossingProbability,
    measureReal_compl (measurableSet_siteSquareRectangleCrossingEvent m n), probReal_univ]
    using h

/-- The elementary polynomial factor in the square-crossing Peierls estimate is absorbed by
`3^n`. -/
theorem two_mul_add_one_le_three_pow (n : ℕ) :
    2 * n + 1 ≤ 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        2 * (n + 1) + 1 ≤ 3 * (2 * n + 1) := by omega
        _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (n + 1) := by rw [pow_succ]; ring

/-- A concrete high-density threshold for the site-crossing estimate (7.70). -/
noncomputable def siteSquareCrossingPeierlsThreshold : ℝ := 15 / 16

/-- A concrete positive rate for the site-crossing estimate (7.70). -/
noncomputable def siteSquareCrossingPeierlsRate : ℝ := -Real.log (3 / 4)

theorem siteSquareCrossingPeierlsThreshold_mem_Ioo :
    siteSquareCrossingPeierlsThreshold ∈ Set.Ioo (0 : ℝ) 1 := by
  norm_num [siteSquareCrossingPeierlsThreshold]

theorem siteSquareCrossingPeierlsRate_pos :
    0 < siteSquareCrossingPeierlsRate := by
  rw [siteSquareCrossingPeierlsRate, neg_pos]
  exact Real.log_neg (by norm_num) (by norm_num)

/-- The explicit Peierls bound is at most a fixed geometric sequence above the concrete
high-density threshold. -/
theorem one_sub_siteSquareCrossingProbability_le_three_quarters_pow
    (p : I) (hp : siteSquareCrossingPeierlsThreshold < (p : ℝ))
    (n : ℕ) (hn : 0 < n) :
    1 - siteSquareRectangleCrossingProbability p (2 * n) n ≤
      (3 / 4 : ℝ) ^ n := by
  let q : ℝ := 1 - (p : ℝ)
  have hq0 : 0 ≤ q := sub_nonneg.mpr p.2.2
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [p.2.1]
  have hqLt : q < (1 / 16 : ℝ) := by
    dsimp [q, siteSquareCrossingPeierlsThreshold] at hp ⊢
    linarith
  have hqSq : q ^ 2 < (1 / 16 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hq0 (by norm_num)).2 hqLt
  have hbaseNonneg : 0 ≤ 192 * q ^ 2 := by positivity
  have hbaseLe : 192 * q ^ 2 ≤ (3 / 4 : ℝ) := by
    nlinarith
  have hcardReal : ((2 * n + 1 : ℕ) : ℝ) ≤ (3 : ℝ) ^ n := by
    exact_mod_cast two_mul_add_one_le_three_pow n
  have h8 : (8 : ℝ) ^ (2 * n) = (64 : ℝ) ^ n := by
    rw [pow_mul]
    norm_num
  have hqPow : q ^ (2 * n + 1) = (q ^ 2) ^ n * q := by
    rw [pow_add, pow_mul]
    ring
  calc
    1 - siteSquareRectangleCrossingProbability p (2 * n) n ≤
        (((2 * n + 1 : ℕ) : ℝ) * (8 : ℝ) ^ (2 * n) * q ^ (2 * n + 1)) := by
      simpa [q, Nat.mul_add] using
        one_sub_siteSquareRectangleCrossingProbability_le p (2 * n) n hn
    _ = ((2 * n + 1 : ℕ) : ℝ) * q * (64 * q ^ 2) ^ n := by
      rw [h8, hqPow, mul_pow]
      ring
    _ ≤ (3 : ℝ) ^ n * 1 * (64 * q ^ 2) ^ n := by
      gcongr
    _ = (192 * q ^ 2) ^ n := by
      simp only [mul_one]
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ (3 / 4 : ℝ) ^ n :=
      pow_le_pow_left₀ hbaseNonneg hbaseLe n

/-- Grimmett (7.70), in the translated rectangle coordinates used by the library: above one
fixed density `α < 1`, every square of half-width `n ≥ 1` has an open left-right crossing with
probability at least `1 - exp (-ρ n)` for a fixed `ρ > 0`.

The source permits `ρ` to depend on `p`; the proved rate is uniform for all densities above the
displayed threshold, which is stronger. -/
theorem siteSquareCrossingProbability_ge_one_sub_exp
    (p : I) (hp : siteSquareCrossingPeierlsThreshold < (p : ℝ))
    (n : ℕ) (hn : 1 ≤ n) :
    1 - Real.exp (-siteSquareCrossingPeierlsRate * (n : ℝ)) ≤
      siteSquareRectangleCrossingProbability p (2 * n) n := by
  have hfailure := one_sub_siteSquareCrossingProbability_le_three_quarters_pow
    p hp n hn
  have hexp : (3 / 4 : ℝ) ^ n =
      Real.exp (-siteSquareCrossingPeierlsRate * (n : ℝ)) := by
    rw [siteSquareCrossingPeierlsRate]
    have harg : - -Real.log (3 / 4) * (n : ℝ) =
        (n : ℝ) * Real.log (3 / 4) := by ring
    rw [harg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hexp] at hfailure
  linarith

end Percolation
