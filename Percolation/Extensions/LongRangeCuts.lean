import Percolation.Extensions.LongRangeErgodicity

/-!
# Cut events for one-dimensional long-range percolation

This file formalizes criterion (12.1) in Grimmett, *Percolation* (2nd ed.): if
`∑ n * p(n)` is finite, then every component of the one-dimensional long-range graph is
almost surely finite.  The proof follows the book's cut argument.  We enumerate exactly the
`n` bonds of length `n` crossing an integer cut, prove that one cut has positive probability,
and use the finite-cylinder weak law from `LongRangeErgodicity` to obtain cuts arbitrarily far
in both directions.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

/-- The unordered bond of length `n` whose left endpoint is `i` sites to the left of the cut
between `k` and `k+1`.  The type `Fin n` records that there are exactly `n` such bonds. -/
def longRangeCutEdge (k : ℤ) (n : ℕ) (i : Fin n) : Sym2 ℤ :=
  s(k - ((i : ℕ) : ℤ), k - ((i : ℕ) : ℤ) + n)

@[simp]
theorem longRangeEdgeDistance_cutEdge (k : ℤ) (n : ℕ) (i : Fin n) :
    longRangeEdgeDistance (longRangeCutEdge k n i) = n := by
  simp [longRangeCutEdge]

/-- A bond has endpoints on opposite sides of the integer cut after `k`. -/
def longRangeEdgeCrossesCut (k : ℤ) : Sym2 ℤ → Prop :=
  Sym2.lift ⟨fun x y ↦ (x ≤ k ∧ k < y) ∨ (y ≤ k ∧ k < x), by
    intro x y
    aesop⟩

@[simp]
theorem longRangeEdgeCrossesCut_mk (k x y : ℤ) :
    longRangeEdgeCrossesCut k s(x, y) ↔
      (x ≤ k ∧ k < y) ∨ (y ≤ k ∧ k < x) := by
  rfl

theorem longRangeEdgeCrossesCut_cutEdge (k : ℤ) (n : ℕ) (i : Fin n) :
    longRangeEdgeCrossesCut k (longRangeCutEdge k n i) := by
  simp only [longRangeCutEdge, longRangeEdgeCrossesCut_mk]
  left
  constructor <;> omega

/-- Every bond crossing a cut occurs uniquely among the canonical length-indexed bonds.  Only
existence is needed by the probability argument; uniqueness is exposed separately below. -/
theorem longRangeEdgeCrossesCut_iff_exists_cutEdge (k : ℤ) (e : Sym2 ℤ) :
    longRangeEdgeCrossesCut k e ↔
      ∃ n : ℕ, ∃ i : Fin n, e = longRangeCutEdge k n i := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [longRangeEdgeCrossesCut_mk]
      constructor
      · intro h
        rcases h with h | h
        · let n : ℕ := (y - x).natAbs
          have hnZ : ((n : ℕ) : ℤ) = y - x := by
            rw [Int.natCast_natAbs]
            exact abs_of_nonneg (sub_nonneg.mpr (h.1.trans h.2.le))
          have hnpos : 0 < n := by
            rw [Int.natAbs_pos]
            omega
          let i : Fin n := ⟨(k - x).natAbs, by
            dsimp [n]
            exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (sub_nonneg.mpr h.1) (by omega)⟩
          refine ⟨n, i, ?_⟩
          rw [longRangeCutEdge]
          have hiZ : (((i : Fin n) : ℕ) : ℤ) = k - x := by
            dsimp [i]
            rw [Int.natCast_natAbs]
            exact abs_of_nonneg (sub_nonneg.mpr h.1)
          rw [hiZ, hnZ]
          congr 1 <;> omega
        · let n : ℕ := (x - y).natAbs
          have hnZ : ((n : ℕ) : ℤ) = x - y := by
            rw [Int.natCast_natAbs]
            exact abs_of_nonneg (sub_nonneg.mpr (h.1.trans h.2.le))
          have hnpos : 0 < n := by
            rw [Int.natAbs_pos]
            omega
          let i : Fin n := ⟨(k - y).natAbs, by
            dsimp [n]
            exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (sub_nonneg.mpr h.1) (by omega)⟩
          refine ⟨n, i, ?_⟩
          rw [longRangeCutEdge]
          have hiZ : (((i : Fin n) : ℕ) : ℤ) = k - y := by
            dsimp [i]
            rw [Int.natCast_natAbs]
            exact abs_of_nonneg (sub_nonneg.mpr h.1)
          rw [hiZ, hnZ]
          rw [Sym2.eq_swap]
          congr 1 <;> omega
      · rintro ⟨n, i, hEq⟩
        change longRangeEdgeCrossesCut k s(x, y)
        rw [hEq]
        exact longRangeEdgeCrossesCut_cutEdge k n i

/-- The set of all bonds crossing the cut after `k`. -/
def longRangeCutEdges (k : ℤ) : Set (Sym2 ℤ) :=
  {e | longRangeEdgeCrossesCut k e}

/-- No open bond crosses the cut after `k`. -/
def longRangeCutEvent (k : ℤ) : Set LongRangeConfiguration :=
  {ω | Disjoint (longRangeCutEdges k) ω}

theorem mem_longRangeCutEvent_iff (k : ℤ) (ω : LongRangeConfiguration) :
    ω ∈ longRangeCutEvent k ↔
      ∀ n : ℕ, ∀ i : Fin n, longRangeCutEdge k n i ∉ ω := by
  rw [longRangeCutEvent, Set.mem_setOf_eq, Set.disjoint_left]
  constructor
  · intro h n i hmem
    exact h (longRangeEdgeCrossesCut_cutEdge k n i) hmem
  · intro h e he hmem
    obtain ⟨n, i, rfl⟩ :=
      (longRangeEdgeCrossesCut_iff_exists_cutEdge k e).mp he
    exact h n i hmem

theorem measurableSet_longRangeCutEvent (k : ℤ) :
    MeasurableSet (longRangeCutEvent k) := by
  rw [show longRangeCutEvent k =
      ⋂ n : ℕ, ⋂ i : Fin n,
        {ω : LongRangeConfiguration | longRangeCutEdge k n i ∉ ω} by
    ext ω
    simp [mem_longRangeCutEvent_iff]]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun i ↦
    (measurableSet_coordinateEvent (longRangeCutEdge k n i)).compl

/-- A dependent index for a crossing bond of length at most `N`. -/
abbrev LongRangeCutIndexUpTo (N : ℕ) :=
  Σ n : Fin (N + 1), Fin n.val

/-- The finite family of crossing bonds having length at most `N`. -/
noncomputable def longRangeCutEdgesUpTo (k : ℤ) (N : ℕ) : Finset (Sym2 ℤ) :=
  Finset.univ.image fun z : LongRangeCutIndexUpTo N ↦
    longRangeCutEdge k z.1.val z.2

theorem mem_longRangeCutEdgesUpTo_iff (k : ℤ) (N : ℕ) (e : Sym2 ℤ) :
    e ∈ longRangeCutEdgesUpTo k N ↔
      ∃ n ≤ N, ∃ i : Fin n, e = longRangeCutEdge k n i := by
  classical
  rw [longRangeCutEdgesUpTo, Finset.mem_image]
  constructor
  · rintro ⟨z, _hz, rfl⟩
    exact ⟨z.1.val, Nat.le_of_lt_succ z.1.isLt, z.2, rfl⟩
  · rintro ⟨n, hn, i, rfl⟩
    let z : LongRangeCutIndexUpTo N :=
      ⟨⟨n, Nat.lt_succ_iff.mpr hn⟩, i⟩
    exact ⟨z, Finset.mem_univ z, rfl⟩

theorem longRangeEdgeDistance_le_of_mem_cutEdgesUpTo
    {k : ℤ} {N : ℕ} {e : Sym2 ℤ} (he : e ∈ longRangeCutEdgesUpTo k N) :
    longRangeEdgeDistance e ≤ N := by
  obtain ⟨n, hn, i, rfl⟩ := (mem_longRangeCutEdgesUpTo_iff k N e).mp he
  simpa using hn

/-- The finite-cylinder event that every crossing bond of length at most `N` is closed. -/
def longRangeFiniteCutEvent (k : ℤ) (N : ℕ) : Set LongRangeConfiguration :=
  {ω | Disjoint (longRangeCutEdgesUpTo k N : Set (Sym2 ℤ)) ω}

theorem measurableSet_longRangeFiniteCutEvent (k : ℤ) (N : ℕ) :
    MeasurableSet (longRangeFiniteCutEvent k N) :=
  measurableSet_disjoint_finset (longRangeCutEdgesUpTo k N)

/-- Some crossing bond whose length is strictly larger than `N` is open.  Writing its length
as `N+1+j` makes the tail probability a literal shifted series. -/
def longRangeCutTailOpenEvent (k : ℤ) (N : ℕ) : Set LongRangeConfiguration :=
  {ω | ∃ j : ℕ, ∃ i : Fin (N + 1 + j),
    longRangeCutEdge k (N + 1 + j) i ∈ ω}

theorem measurableSet_longRangeCutTailOpenEvent (k : ℤ) (N : ℕ) :
    MeasurableSet (longRangeCutTailOpenEvent k N) := by
  rw [show longRangeCutTailOpenEvent k N =
      ⋃ j : ℕ, ⋃ i : Fin (N + 1 + j),
        {ω : LongRangeConfiguration |
          longRangeCutEdge k (N + 1 + j) i ∈ ω} by
    ext ω
    simp [longRangeCutTailOpenEvent]]
  exact MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun i ↦
    measurableSet_coordinateEvent (longRangeCutEdge k (N + 1 + j) i)

theorem longRangeCutEvent_eq_finite_inter_tailCompl (k : ℤ) (N : ℕ) :
    longRangeCutEvent k =
      longRangeFiniteCutEvent k N ∩ (longRangeCutTailOpenEvent k N)ᶜ := by
  ext ω
  rw [mem_longRangeCutEvent_iff]
  simp only [Set.mem_inter_iff, longRangeFiniteCutEvent, Set.mem_setOf_eq,
    Set.mem_compl_iff, longRangeCutTailOpenEvent, not_exists]
  rw [Set.disjoint_left]
  constructor
  · intro h
    constructor
    · intro e he hω
      obtain ⟨n, _hn, i, rfl⟩ := (mem_longRangeCutEdgesUpTo_iff k N e).mp he
      exact h n i hω
    · intro j i
      exact h (N + 1 + j) i
  · rintro ⟨hfinite, htail⟩ n i
    by_cases hn : n ≤ N
    · exact hfinite ((mem_longRangeCutEdgesUpTo_iff k N _).mpr
        ⟨n, hn, i, rfl⟩)
    · let j := n - (N + 1)
      have hnj : N + 1 + j = n := by
        dsimp [j]
        omega
      let i' : Fin (N + 1 + j) := Fin.cast hnj.symm i
      have hclosed := htail j i'
      simpa [i', longRangeCutEdge, hnj] using hclosed

/-- The coordinate block containing all crossing edges longer than `N`. -/
def longRangeCutTailEdges (k : ℤ) (N : ℕ) : Set (Sym2 ℤ) :=
  {e | longRangeEdgeCrossesCut k e ∧ N < longRangeEdgeDistance e}

theorem disjoint_cutEdgesUpTo_cutTailEdges (k : ℤ) (N : ℕ) :
    Disjoint (longRangeCutEdgesUpTo k N : Set (Sym2 ℤ))
      (longRangeCutTailEdges k N) := by
  rw [Set.disjoint_left]
  intro e he htail
  exact (not_lt_of_ge (longRangeEdgeDistance_le_of_mem_cutEdgesUpTo he)) htail.2

theorem measurableSet_longRangeFiniteCutEvent_generateFrom (k : ℤ) (N : ℕ) :
    MeasurableSet[MeasurableSpace.generateFrom
      (coordinateEvents (longRangeCutEdgesUpTo k N : Set (Sym2 ℤ)))]
      (longRangeFiniteCutEvent k N) := by
  have hdep : DependsOn (longRangeCutEdgesUpTo k N)
      (longRangeFiniteCutEvent k N) := by
    intro ω η h
    simp only [longRangeFiniteCutEvent, Set.mem_setOf_eq, Set.disjoint_left]
    exact forall_congr' fun e ↦ forall_congr' fun he ↦ not_congr (h e he)
  exact hdep.measurableSet_generateFrom_coordinateEvents Set.Subset.rfl

theorem measurableSet_longRangeCutTailOpenEvent_generateFrom (k : ℤ) (N : ℕ) :
    MeasurableSet[MeasurableSpace.generateFrom
      (coordinateEvents (longRangeCutTailEdges k N))]
      (longRangeCutTailOpenEvent k N) := by
  rw [show longRangeCutTailOpenEvent k N =
      ⋃ j : ℕ, ⋃ i : Fin (N + 1 + j),
        {ω : LongRangeConfiguration |
          longRangeCutEdge k (N + 1 + j) i ∈ ω} by
    ext ω
    simp [longRangeCutTailOpenEvent]]
  refine MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun i ↦
    MeasurableSpace.measurableSet_generateFrom ?_
  refine ⟨longRangeCutEdge k (N + 1 + j) i, ?_, rfl⟩
  exact ⟨longRangeEdgeCrossesCut_cutEdge _ _ _, by
    rw [longRangeEdgeDistance_cutEdge]
    omega⟩

/-- The finite and tail portions of a cut use disjoint coordinate blocks. -/
theorem indepSet_longRangeFiniteCutEvent_cutTailCompl
    (p : LongRangeProfile) (k : ℤ) (N : ℕ) :
    IndepSet (longRangeFiniteCutEvent k N)
      (longRangeCutTailOpenEvent k N)ᶜ (longRangeMeasure p) := by
  change IndepSet _ _ (inhomogeneousSetBernoulli (longRangeEdgeDensity p))
  have hindep := indep_generateFrom_coordinateEvents_inhomogeneous
    (longRangeEdgeDensity p) (disjoint_cutEdgesUpTo_cutTailEdges k N)
  apply hindep.indepSet_of_measurableSet
  · exact measurableSet_longRangeFiniteCutEvent_generateFrom k N
  · exact (measurableSet_longRangeCutTailOpenEvent_generateFrom k N).compl

/-! ### Probability estimates -/

/-- A real-valued countable union bound with a supplied summable majorant. -/
theorem measureReal_iUnion_nat_le_tsum_of_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hbsum : Summable b) (hA : ∀ n, μ.real (A n) ≤ b n) :
    μ.real (⋃ n, A n) ≤ ∑' n, b n := by
  have hmeasure : μ (⋃ n, A n) ≤ ∑' n, ENNReal.ofReal (b n) := by
    refine (measure_iUnion_le A).trans (ENNReal.tsum_le_tsum fun n ↦ ?_)
    calc
      μ (A n) = ENNReal.ofReal (μ.real (A n)) := by
        exact (ENNReal.ofReal_toReal (measure_ne_top μ (A n))).symm
      _ ≤ ENNReal.ofReal (b n) := ENNReal.ofReal_le_ofReal (hA n)
  have hfinite : ∑' n, ENNReal.ofReal (b n) ≠ ⊤ :=
    hbsum.tsum_ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)] at hreal
  simpa only [Measure.real, ENNReal.toReal_ofReal (hb _)] using hreal

/-- At least one of the `n` bonds of length `n` crossing the cut is open. -/
def longRangeCutLengthOpenEvent (k : ℤ) (n : ℕ) : Set LongRangeConfiguration :=
  {ω | ∃ i : Fin n, longRangeCutEdge k n i ∈ ω}

theorem measurableSet_longRangeCutLengthOpenEvent (k : ℤ) (n : ℕ) :
    MeasurableSet (longRangeCutLengthOpenEvent k n) := by
  rw [show longRangeCutLengthOpenEvent k n =
      ⋃ i : Fin n, {ω : LongRangeConfiguration | longRangeCutEdge k n i ∈ ω} by
    ext ω
    simp [longRangeCutLengthOpenEvent]]
  exact MeasurableSet.iUnion fun i ↦ measurableSet_coordinateEvent _

/-- Union bound for the `n` length-`n` bonds crossing one cut. -/
theorem longRangeMeasure_real_cutLengthOpenEvent_le
    (p : LongRangeProfile) (k : ℤ) (n : ℕ) :
    (longRangeMeasure p).real (longRangeCutLengthOpenEvent k n) ≤
      (n : ℝ) * (p n : ℝ) := by
  rw [show longRangeCutLengthOpenEvent k n =
      ⋃ i : Fin n, {ω : LongRangeConfiguration | longRangeCutEdge k n i ∈ ω} by
    ext ω
    simp [longRangeCutLengthOpenEvent]]
  calc
    (longRangeMeasure p).real
        (⋃ i : Fin n, {ω : LongRangeConfiguration | longRangeCutEdge k n i ∈ ω}) ≤
        ∑ i : Fin n, (longRangeMeasure p).real
          {ω : LongRangeConfiguration | longRangeCutEdge k n i ∈ ω} :=
      measureReal_iUnion_fintype_le _
    _ = ∑ _i : Fin n, (p n : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [longRangeMeasure_real_edgeOpen, longRangeEdgeDensity,
        longRangeEdgeDistance_cutEdge]
    _ = (n : ℝ) * (p n : ℝ) := by simp

theorem longRangeCutTailOpenEvent_eq_iUnion_length (k : ℤ) (N : ℕ) :
    longRangeCutTailOpenEvent k N =
      ⋃ j : ℕ, longRangeCutLengthOpenEvent k (N + 1 + j) := by
  ext ω
  simp [longRangeCutTailOpenEvent, longRangeCutLengthOpenEvent]

/-- The chance of an open crossing edge longer than `N` is bounded by the shifted weighted
tail from Grimmett's display (12.1). -/
theorem longRangeMeasure_real_cutTailOpenEvent_le
    (p : LongRangeProfile) (k : ℤ) (N : ℕ)
    (hsum : Summable fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) :
    (longRangeMeasure p).real (longRangeCutTailOpenEvent k N) ≤
      ∑' j : ℕ, ((N + 1 + j : ℕ) : ℝ) * (p (N + 1 + j) : ℝ) := by
  rw [longRangeCutTailOpenEvent_eq_iUnion_length]
  apply measureReal_iUnion_nat_le_tsum_of_le
  · intro j
    exact mul_nonneg (Nat.cast_nonneg _) (unitInterval.nonneg _)
  · exact hsum.comp_injective (fun a b h ↦ by omega)
  · intro j
    exact longRangeMeasure_real_cutLengthOpenEvent_le p k (N + 1 + j)

theorem longRangeMeasure_real_finiteCutEvent (p : LongRangeProfile) (k : ℤ) (N : ℕ) :
    (longRangeMeasure p).real (longRangeFiniteCutEvent k N) =
      ∏ e ∈ longRangeCutEdgesUpTo k N,
        (1 - (p (longRangeEdgeDistance e) : ℝ)) := by
  exact longRangeMeasure_real_disjoint_finset p (longRangeCutEdgesUpTo k N)

/-- Under the source convention `p(n)<1`, every finite part of a cut has positive
probability. -/
theorem longRangeMeasure_real_finiteCutEvent_pos
    (p : LongRangeProfile) (hp : p.IsStrict) (k : ℤ) (N : ℕ) :
    0 < (longRangeMeasure p).real (longRangeFiniteCutEvent k N) := by
  rw [longRangeMeasure_real_finiteCutEvent]
  apply Finset.prod_pos
  intro e he
  obtain ⟨n, _hn, i, rfl⟩ := (mem_longRangeCutEdgesUpTo_iff k N e).mp he
  rw [longRangeEdgeDistance_cutEdge]
  have hnpos : 0 < n := by
    have hi := i.isLt
    omega
  have hlt := hp n hnpos
  linarith [unitInterval.nonneg (p n)]

/-- A summable weighted profile gives one cut positive probability. -/
theorem longRangeMeasure_real_cutEvent_pos_of_summable_nat_mul
    (p : LongRangeProfile) (hp : p.IsStrict)
    (hsum : Summable fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) (k : ℤ) :
    0 < (longRangeMeasure p).real (longRangeCutEvent k) := by
  let f : ℕ → ℝ := fun n ↦ (n : ℝ) * (p n : ℝ)
  have hfnonneg : ∀ n, 0 ≤ f n := fun n ↦ by
    dsimp [f]
    exact mul_nonneg (Nat.cast_nonneg _) (unitInterval.nonneg _)
  have htail : Tendsto (fun N : ℕ ↦ ∑' j : ℕ, f (j + N)) atTop (nhds 0) :=
    _root_.tendsto_sum_nat_add f
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 htail 1 zero_lt_one
  let N := M
  have htailLt :
      ∑' j : ℕ, ((N + 1 + j : ℕ) : ℝ) * (p (N + 1 + j) : ℝ) < 1 := by
    have hM' := hM (N + 1) (by simp [N])
    rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hM'
    · simpa only [f, add_comm] using hM'
    · exact tsum_nonneg fun j ↦ hfnonneg _
  have hopenLt :
      (longRangeMeasure p).real (longRangeCutTailOpenEvent k N) < 1 :=
    (longRangeMeasure_real_cutTailOpenEvent_le p k N hsum).trans_lt htailLt
  have htailComplPos :
      0 < (longRangeMeasure p).real (longRangeCutTailOpenEvent k N)ᶜ := by
    rw [measureReal_compl (measurableSet_longRangeCutTailOpenEvent k N), probReal_univ]
    linarith
  rw [longRangeCutEvent_eq_finite_inter_tailCompl k N]
  have hfactor :=
    (indepSet_longRangeFiniteCutEvent_cutTailCompl p k N).measure_inter_eq_mul
  have hfactorReal := congrArg ENNReal.toReal hfactor
  rw [ENNReal.toReal_mul] at hfactorReal
  rw [show (longRangeMeasure p).real
      (longRangeFiniteCutEvent k N ∩ (longRangeCutTailOpenEvent k N)ᶜ) =
      (longRangeMeasure p).real (longRangeFiniteCutEvent k N) *
        (longRangeMeasure p).real (longRangeCutTailOpenEvent k N)ᶜ by
    simpa [Measure.real] using hfactorReal]
  exact mul_pos (longRangeMeasure_real_finiteCutEvent_pos p hp k N) htailComplPos

/-! ### Reflection and two-sided recurrence -/

/-- Reflect both endpoints of a long-range bond through the origin. -/
def longRangeEdgeReflectEmbedding : Sym2 ℤ ↪ Sym2 ℤ :=
  (Equiv.neg ℤ).toEmbedding.sym2Map

@[simp]
theorem longRangeEdgeReflectEmbedding_mk (x y : ℤ) :
    longRangeEdgeReflectEmbedding s(x, y) = s(-x, -y) := by
  rfl

@[simp]
theorem longRangeEdgeDistance_reflect (e : Sym2 ℤ) :
    longRangeEdgeDistance (longRangeEdgeReflectEmbedding e) =
      longRangeEdgeDistance e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [longRangeEdgeReflectEmbedding_mk, longRangeEdgeDistance_mk]
      rw [show -y - -x = -(y - x) by ring, Int.natAbs_neg]

@[simp]
theorem longRangeEdgeReflectEmbedding_involutive (e : Sym2 ℤ) :
    longRangeEdgeReflectEmbedding (longRangeEdgeReflectEmbedding e) = e := by
  induction e using Sym2.inductionOn with
  | _ x y => simp

/-- Pull a configuration back under reflection. -/
def longRangeReflectionPullback (ω : LongRangeConfiguration) :
    LongRangeConfiguration :=
  longRangeEdgeReflectEmbedding ⁻¹' ω

theorem measurable_longRangeReflectionPullback :
    Measurable longRangeReflectionPullback :=
  measurable_preimage_embedding longRangeEdgeReflectEmbedding

/-- The distance-dependent product law is reflection invariant. -/
theorem longRangeMeasure_map_reflectionPullback (p : LongRangeProfile) :
    (longRangeMeasure p).map longRangeReflectionPullback = longRangeMeasure p := by
  change (inhomogeneousSetBernoulli (longRangeEdgeDensity p)).map
      (fun ω ↦ longRangeEdgeReflectEmbedding ⁻¹' ω) =
    inhomogeneousSetBernoulli (longRangeEdgeDensity p)
  rw [inhomogeneousSetBernoulli_map_preimage_embedding]
  congr 1
  funext e
  simp [longRangeEdgeDensity]

theorem longRangeEdgeCrossesCut_reflect_iff (k : ℤ) (e : Sym2 ℤ) :
    longRangeEdgeCrossesCut k (longRangeEdgeReflectEmbedding e) ↔
      longRangeEdgeCrossesCut (-k - 1) e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [longRangeEdgeReflectEmbedding_mk, longRangeEdgeCrossesCut_mk]
      omega

/-- Reflection sends the cut after `k` to the cut after `-k-1`. -/
theorem longRangeReflectionPullback_preimage_cutEvent (k : ℤ) :
    longRangeReflectionPullback ⁻¹' longRangeCutEvent k =
      longRangeCutEvent (-k - 1) := by
  ext ω
  simp only [Set.mem_preimage, mem_longRangeCutEvent_iff]
  constructor
  · intro h n i hω
    let e := longRangeEdgeReflectEmbedding (longRangeCutEdge (-k - 1) n i)
    have hecross : longRangeEdgeCrossesCut k e :=
      (longRangeEdgeCrossesCut_reflect_iff k _).mpr
        (longRangeEdgeCrossesCut_cutEdge _ _ _)
    obtain ⟨m, j, heq⟩ :=
      (longRangeEdgeCrossesCut_iff_exists_cutEdge k e).mp hecross
    have hclosed := h m j
    apply hclosed
    change longRangeEdgeReflectEmbedding (longRangeCutEdge k m j) ∈ ω
    rw [← heq, longRangeEdgeReflectEmbedding_involutive]
    exact hω
  · intro h n i hω
    let e := longRangeEdgeReflectEmbedding (longRangeCutEdge k n i)
    have hecross : longRangeEdgeCrossesCut (-k - 1) e := by
      have href := longRangeEdgeCrossesCut_reflect_iff (-k - 1)
        (longRangeCutEdge k n i)
      rw [show -(-k - 1) - 1 = k by ring] at href
      exact href.mpr (longRangeEdgeCrossesCut_cutEdge _ _ _)
    obtain ⟨m, j, heq⟩ :=
      (longRangeEdgeCrossesCut_iff_exists_cutEdge (-k - 1) e).mp hecross
    have hclosed := h m j
    apply hclosed
    rw [← heq]
    exact hω

/-- Some cut occurs at or to the left of `m`. -/
def longRangeCutOccursBefore (m : ℤ) : Set LongRangeConfiguration :=
  {ω | ∃ k : ℤ, k ≤ m ∧ ω ∈ longRangeCutEvent k}

theorem measurableSet_longRangeCutOccursBefore (m : ℤ) :
    MeasurableSet (longRangeCutOccursBefore m) := by
  rw [show longRangeCutOccursBefore m =
      ⋃ k : ℤ, if k ≤ m then longRangeCutEvent k else ∅ by
    ext ω
    simp [longRangeCutOccursBefore]]
  exact MeasurableSet.iUnion fun k ↦ by
    split_ifs
    · exact measurableSet_longRangeCutEvent k
    · exact MeasurableSet.empty

@[simp]
theorem longRangeEdgeTranslateEmbedding_cutEdge
    (a k : ℤ) (n : ℕ) (i : Fin n) :
    longRangeEdgeTranslateEmbedding a (longRangeCutEdge k n i) =
      longRangeCutEdge (k + a) n i := by
  simp only [longRangeCutEdge, longRangeEdgeTranslateEmbedding_mk]
  congr 1 <;> ring

theorem longRangeTranslatedEvent_cutEvent (a k : ℤ) :
    longRangeTranslatedEvent a (longRangeCutEvent k) =
      longRangeCutEvent (k + a) := by
  ext ω
  simp only [longRangeTranslatedEvent, Set.mem_preimage,
    mem_longRangeCutEvent_iff]
  constructor
  · intro h n i hi
    apply h n i
    change longRangeEdgeTranslateEmbedding a (longRangeCutEdge k n i) ∈ ω
    rw [longRangeEdgeTranslateEmbedding_cutEdge]
    exact hi
  · intro h n i hi
    change longRangeEdgeTranslateEmbedding a (longRangeCutEdge k n i) ∈ ω at hi
    rw [longRangeEdgeTranslateEmbedding_cutEdge] at hi
    exact h n i hi

theorem longRangeReflectionPullback_preimage_translateOccursEventually_cut
    (m : ℤ) :
    longRangeReflectionPullback ⁻¹'
        longRangeTranslateOccursEventually (longRangeCutEvent 0) (-m - 1) =
      longRangeCutOccursBefore m := by
  ext ω
  simp only [Set.mem_preimage, longRangeTranslateOccursEventually,
    Set.mem_setOf_eq, longRangeCutOccursBefore]
  constructor
  · rintro ⟨a, ha, hcut⟩
    have htranslate : longRangeTranslatedEvent a (longRangeCutEvent 0) =
        longRangeCutEvent a := by
      simpa using longRangeTranslatedEvent_cutEvent a 0
    rw [htranslate] at hcut
    have href : ω ∈ longRangeCutEvent (-a - 1) := by
      rw [← longRangeReflectionPullback_preimage_cutEvent a]
      exact hcut
    exact ⟨-a - 1, by omega, href⟩
  · rintro ⟨k, hk, hcut⟩
    let a := -k - 1
    refine ⟨a, by dsimp [a]; omega, ?_⟩
    have href : longRangeReflectionPullback ω ∈ longRangeCutEvent a := by
      change ω ∈ longRangeReflectionPullback ⁻¹' longRangeCutEvent a
      rw [longRangeReflectionPullback_preimage_cutEvent a]
      simpa [a] using hcut
    have htranslate : longRangeTranslatedEvent a (longRangeCutEvent 0) =
        longRangeCutEvent a := by
      simpa using longRangeTranslatedEvent_cutEvent a 0
    rwa [htranslate]

theorem longRangeMeasure_real_cutOccursBefore_eq_one
    (p : LongRangeProfile) (hp : p.IsStrict)
    (hsum : Summable fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) (m : ℤ) :
    (longRangeMeasure p).real (longRangeCutOccursBefore m) = 1 := by
  let A := longRangeTranslateOccursEventually (longRangeCutEvent 0) (-m - 1)
  have hAmeas : MeasurableSet A :=
    measurableSet_longRangeTranslateOccursEventually
      (measurableSet_longRangeCutEvent 0) _
  have hAone : (longRangeMeasure p).real A = 1 :=
    longRangeMeasure_real_translateOccursEventually_eq_one p
      (measurableSet_longRangeCutEvent 0)
      (longRangeMeasure_real_cutEvent_pos_of_summable_nat_mul p hp hsum 0) _
  have hmap := longRangeMeasure_map_reflectionPullback p
  have happ := congrArg (fun μ : Measure LongRangeConfiguration ↦ μ A) hmap
  change (Measure.map longRangeReflectionPullback (longRangeMeasure p)) A =
    (longRangeMeasure p) A at happ
  rw [Measure.map_apply measurable_longRangeReflectionPullback hAmeas] at happ
  have hpre : longRangeReflectionPullback ⁻¹' A = longRangeCutOccursBefore m :=
    longRangeReflectionPullback_preimage_translateOccursEventually_cut m
  rw [hpre] at happ
  have happReal := congrArg ENNReal.toReal happ
  change ((longRangeMeasure p) (longRangeCutOccursBefore m)).toReal = 1
  calc
    ((longRangeMeasure p) (longRangeCutOccursBefore m)).toReal =
        ((longRangeMeasure p) A).toReal := happReal
    _ = 1 := by simpa only [Measure.real] using hAone

/-- Some cut occurs at or to the right of `m`. -/
def longRangeCutOccursAfter (m : ℤ) : Set LongRangeConfiguration :=
  {ω | ∃ k : ℤ, m ≤ k ∧ ω ∈ longRangeCutEvent k}

theorem longRangeCutOccursAfter_eq_translateOccursEventually (m : ℤ) :
    longRangeCutOccursAfter m =
      longRangeTranslateOccursEventually (longRangeCutEvent 0) m := by
  ext ω
  simp only [longRangeCutOccursAfter, Set.mem_setOf_eq,
    longRangeTranslateOccursEventually]
  apply exists_congr
  intro k
  rw [longRangeTranslatedEvent_cutEvent]
  simp

theorem measurableSet_longRangeCutOccursAfter (m : ℤ) :
    MeasurableSet (longRangeCutOccursAfter m) := by
  rw [longRangeCutOccursAfter_eq_translateOccursEventually]
  exact measurableSet_longRangeTranslateOccursEventually
    (measurableSet_longRangeCutEvent 0) m

theorem longRangeMeasure_real_cutOccursAfter_eq_one
    (p : LongRangeProfile) (hp : p.IsStrict)
    (hsum : Summable fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) (m : ℤ) :
    (longRangeMeasure p).real (longRangeCutOccursAfter m) = 1 := by
  rw [longRangeCutOccursAfter_eq_translateOccursEventually]
  exact longRangeMeasure_real_translateOccursEventually_eq_one p
    (measurableSet_longRangeCutEvent 0)
    (longRangeMeasure_real_cutEvent_pos_of_summable_nat_mul p hp hsum 0) m

/-- An open edge cannot cross a closed cut, so its endpoints lie on the same side. -/
theorem longRangeOpenGraph_adj_sameSide_of_mem_cutEvent
    {ω : LongRangeConfiguration} {k x y : ℤ}
    (hcut : ω ∈ longRangeCutEvent k) (hxy : (longRangeOpenGraph ω).Adj x y) :
    (x ≤ k ↔ y ≤ k) := by
  have hopen : s(x, y) ∈ ω := (longRangeOpenGraph_adj.mp hxy).1
  have hnotCross : ¬ longRangeEdgeCrossesCut k s(x, y) := by
    intro hcross
    exact Set.disjoint_left.mp hcut hcross hopen
  simp only [longRangeEdgeCrossesCut_mk, not_or, not_and_or, not_le] at hnotCross
  omega

theorem longRangeOpenGraph_walk_sameSide_of_mem_cutEvent
    {ω : LongRangeConfiguration} {k x y : ℤ}
    (hcut : ω ∈ longRangeCutEvent k) (w : (longRangeOpenGraph ω).Walk x y) :
    (x ≤ k ↔ y ≤ k) := by
  induction w with
  | nil => rfl
  | @cons u v z huv p ih =>
      exact (longRangeOpenGraph_adj_sameSide_of_mem_cutEvent hcut huv).trans ih

theorem longRangeOpenGraph_reachable_sameSide_of_mem_cutEvent
    {ω : LongRangeConfiguration} {k x y : ℤ}
    (hcut : ω ∈ longRangeCutEvent k)
    (hxy : (longRangeOpenGraph ω).Reachable x y) :
    (x ≤ k ↔ y ≤ k) := by
  obtain ⟨w⟩ := hxy
  exact longRangeOpenGraph_walk_sameSide_of_mem_cutEvent hcut w

/-- A left and right cut trap the whole component of `x` in a finite integer interval. -/
theorem longRangeCluster_finite_of_cuts
    {ω : LongRangeConfiguration} {l r x : ℤ}
    (hlx : l < x) (hxr : x ≤ r)
    (hl : ω ∈ longRangeCutEvent l) (hr : ω ∈ longRangeCutEvent r) :
    (longRangeCluster ω x).Finite := by
  apply (Set.finite_Icc (l + 1) r).subset
  intro y hy
  have hreach : (longRangeOpenGraph ω).Reachable x y := by
    exact longRangeOpenGraph_reachable_iff.mpr
      (mem_longRangeCluster_iff.mp hy)
  have hleft := longRangeOpenGraph_reachable_sameSide_of_mem_cutEvent hl hreach
  have hright := longRangeOpenGraph_reachable_sameSide_of_mem_cutEvent hr hreach
  constructor
  · have hnyl : ¬ y ≤ l := by
      intro hyl
      exact (not_le_of_gt hlx) (hleft.mpr hyl)
    omega
  · exact hright.mp hxr

theorem ae_mem_of_measureReal_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : MeasurableSet A) (hAone : μ.real A = 1) :
    ∀ᵐ ω ∂μ, ω ∈ A := by
  rw [ae_mem_iff_measure_eq hA.nullMeasurableSet]
  rw [show μ Set.univ = 1 by simp]
  rw [← ENNReal.toReal_eq_one_iff, ← Measure.real]
  exact hAone

/-- **Grimmett, criterion (12.1).**  If `∑ n p(n)<∞` and every positive-distance density is
strictly below one, every component of the one-dimensional long-range graph is almost surely
finite. -/
theorem longRange_ae_all_components_finite_of_summable_nat_mul
    (p : LongRangeProfile) (hp : p.IsStrict)
    (hsum : Summable fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) :
    ∀ᵐ ω ∂longRangeMeasure p, ω ∈ longRangeAllComponentsFiniteEvent := by
  have hleft : ∀ m : ℤ, ∀ᵐ ω ∂longRangeMeasure p,
      ω ∈ longRangeCutOccursBefore m := fun m ↦
    ae_mem_of_measureReal_eq_one (longRangeMeasure p)
      (measurableSet_longRangeCutOccursBefore m)
      (longRangeMeasure_real_cutOccursBefore_eq_one p hp hsum m)
  have hright : ∀ m : ℤ, ∀ᵐ ω ∂longRangeMeasure p,
      ω ∈ longRangeCutOccursAfter m := fun m ↦
    ae_mem_of_measureReal_eq_one (longRangeMeasure p)
      (measurableSet_longRangeCutOccursAfter m)
      (longRangeMeasure_real_cutOccursAfter_eq_one p hp hsum m)
  have hleftAll : ∀ᵐ ω ∂longRangeMeasure p, ∀ m : ℤ,
      ω ∈ longRangeCutOccursBefore m := ae_all_iff.mpr hleft
  have hrightAll : ∀ᵐ ω ∂longRangeMeasure p, ∀ m : ℤ,
      ω ∈ longRangeCutOccursAfter m := ae_all_iff.mpr hright
  filter_upwards [hleftAll, hrightAll] with ω hωleft hωright
  intro x
  obtain ⟨l, hl, hlcut⟩ := hωleft (x - 1)
  obtain ⟨r, hr, hrcut⟩ := hωright x
  exact longRangeCluster_finite_of_cuts (by omega) hr hlcut hrcut

/-- Probability-one event form of criterion (12.1). -/
theorem longRangeMeasure_real_allComponentsFinite_eq_one_of_summable_nat_mul
    (p : LongRangeProfile) (hp : p.IsStrict)
    (hsum : Summable fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) :
    (longRangeMeasure p).real longRangeAllComponentsFiniteEvent = 1 := by
  have hae := longRange_ae_all_components_finite_of_summable_nat_mul p hp hsum
  rw [ae_mem_iff_measure_eq measurableSet_longRangeAllComponentsFiniteEvent.nullMeasurableSet]
    at hae
  rw [show (longRangeMeasure p) Set.univ = 1 by simp] at hae
  change ((longRangeMeasure p) longRangeAllComponentsFiniteEvent).toReal = 1
  rw [ENNReal.toReal_eq_one_iff]
  exact hae

end Percolation
