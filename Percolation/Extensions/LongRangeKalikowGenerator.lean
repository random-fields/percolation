import Percolation.Extensions.LongRangeKalikow
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Kalikow connectivity for an arbitrary supported generator

This file removes the temporary `p₁ > 0` normalization from the finite-component proof.  For
each positive length `r`, it repeats only the insertion layer on the interval `0,...,r+m`; the
component-count telescope and analytic estimates are reused from `LongRangeKalikow`.
-/

namespace Percolation

open Filter MeasureTheory ProbabilityTheory SimpleGraph
open scoped BigOperators unitInterval

def longRangeGeneratorEdge (r : ℕ) : Sym2 ℤ := s(0, (r : ℤ))

def longRangeEraseGeneratorEdge (r : ℕ) (ω : LongRangeConfiguration) :
    LongRangeConfiguration := ω \ {longRangeGeneratorEdge r}

/-- The preceding component-count index; the explored interval has maximum vertex
`longRangeGeneratorIntervalBase r m + 1`. -/
def longRangeGeneratorIntervalBase (r m : ℕ) : ℕ := r + m - 1

@[simp]
theorem mem_longRangeEraseGeneratorEdge_iff {r : ℕ} {e : Sym2 ℤ}
    {ω : LongRangeConfiguration} :
    e ∈ longRangeEraseGeneratorEdge r ω ↔
      e ∈ ω ∧ e ≠ longRangeGeneratorEdge r := by
  simp [longRangeEraseGeneratorEdge]

/-- Target-generator disconnection after its direct edge is forced closed. -/
def longRangeGeneratorClosedDisconnectionEvent (r m : ℕ) :
  Set LongRangeConfiguration :=
  {ω | ¬(longRangeIntervalOpenGraph
    (longRangeEraseGeneratorEdge r ω) (longRangeGeneratorIntervalBase r m + 1)).Reachable
      0 ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩}

/-- An origin edge longer than the chosen generator but still inside `0,...,r+m`. -/
def longRangeGeneratorLongEdgeEvent (r m : ℕ) : Set LongRangeConfiguration :=
  {ω | ∃ i : Fin (longRangeGeneratorIntervalBase r m + 2), r < i.val ∧
    (longRangeIntervalOpenGraph ω (longRangeGeneratorIntervalBase r m + 1)).Adj 0 i}

/-- Actual target-generator disconnection in the same interval. -/
def longRangeGeneratorDisconnectionEvent (r m : ℕ) : Set LongRangeConfiguration :=
  {ω | ¬(longRangeIntervalOpenGraph ω
    (longRangeGeneratorIntervalBase r m + 1)).Reachable
    0 ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩}

theorem dependsOn_longRangeGeneratorDisconnectionEvent (r m : ℕ) :
    DependsOn (longRangeIntervalEdgeSupport (longRangeGeneratorIntervalBase r m + 1))
      (longRangeGeneratorDisconnectionEvent r m) := by
  intro ω η h
  have hgraph := dependsOnFun_longRangeIntervalOpenGraph
    (longRangeGeneratorIntervalBase r m + 1) h
  change longRangeIntervalOpenGraph ω (longRangeGeneratorIntervalBase r m + 1) =
    longRangeIntervalOpenGraph η (longRangeGeneratorIntervalBase r m + 1) at hgraph
  change (¬(longRangeIntervalOpenGraph ω
      (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
        ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩) ↔
    ¬(longRangeIntervalOpenGraph η
      (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
        ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩
  rw [hgraph]

theorem measurableSet_longRangeGeneratorDisconnectionEvent (r m : ℕ) :
    MeasurableSet (longRangeGeneratorDisconnectionEvent r m) :=
  (dependsOn_longRangeGeneratorDisconnectionEvent r m).measurableSet

theorem longRangeGenerator_insertion_subset_merge
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    longRangeGeneratorClosedDisconnectionEvent r m ∩
        longRangeGeneratorLongEdgeEvent r m ∩
        {ω | longRangeGeneratorEdge r ∈ ω} ⊆
      longRangeIntervalMergeEvent (r + m - 1) := by
  intro ω hω
  rcases hω with ⟨⟨hdis, i, hi, h0i⟩, hropen⟩
  let G := longRangeIntervalOpenGraph ω (longRangeGeneratorIntervalBase r m + 1)
  let H := G.induce ({0}ᶜ : Set (Fin (longRangeGeneratorIntervalBase r m + 2)))
  let rV : Fin (longRangeGeneratorIntervalBase r m + 2) :=
    ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩
  let rH : {x : Fin (longRangeGeneratorIntervalBase r m + 2) //
      x ∈ ({0}ᶜ : Set (Fin (longRangeGeneratorIntervalBase r m + 2)))} :=
    ⟨rV, by simp [rV, hr.ne']⟩
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    simp at hi
  let iH : {x : Fin (longRangeGeneratorIntervalBase r m + 2) //
      x ∈ ({0}ᶜ : Set (Fin (longRangeGeneratorIntervalBase r m + 2)))} :=
    ⟨i, by simpa using hi0⟩
  have h0r : G.Adj 0 rV := by
    rw [longRangeIntervalOpenGraph_adj]
    refine ⟨?_, by simp [rV, hr.ne']⟩
    simpa [longRangeGeneratorEdge, rV] using hropen
  have hnotreach : ¬H.Reachable rH iH := by
    intro hreach
    let F : H →g longRangeIntervalOpenGraph
        (longRangeEraseGeneratorEdge r ω)
          (longRangeGeneratorIntervalBase r m + 1) := {
      toFun := fun x : {x : Fin (longRangeGeneratorIntervalBase r m + 2) //
        x ∈ ({0}ᶜ : Set (Fin (longRangeGeneratorIntervalBase r m + 2)))} ↦ x.1
      map_rel' := by
        intro x y hxy
        change (longRangeIntervalOpenGraph ω
          (longRangeGeneratorIntervalBase r m + 1)).Adj x.1 y.1 at hxy
        rw [longRangeIntervalOpenGraph_adj] at hxy
        rw [longRangeIntervalOpenGraph_adj]
        refine ⟨?_, hxy.2⟩
        rw [mem_longRangeEraseGeneratorEdge_iff]
        refine ⟨hxy.1, ?_⟩
        intro heq
        rcases Sym2.eq_iff.mp heq with heq | heq
        · exact x.property (by simpa [longRangeGeneratorEdge] using heq.1)
        · exact y.property (by simpa [longRangeGeneratorEdge] using heq.2)
    }
    have hri := hreach.map F
    have h0iClosed : (longRangeIntervalOpenGraph
        (longRangeEraseGeneratorEdge r ω)
          (longRangeGeneratorIntervalBase r m + 1)).Adj 0 i := by
      rw [longRangeIntervalOpenGraph_adj] at h0i ⊢
      refine ⟨?_, h0i.2⟩
      rw [mem_longRangeEraseGeneratorEdge_iff]
      refine ⟨h0i.1, ?_⟩
      intro heq
      rcases Sym2.eq_iff.mp heq with heq | heq <;>
        simp [longRangeGeneratorEdge] at heq <;> omega
    change ¬(longRangeIntervalOpenGraph
      (longRangeEraseGeneratorEdge r ω)
        (longRangeGeneratorIntervalBase r m + 1)).Reachable 0 rV at hdis
    exact hdis (h0iClosed.reachable.trans hri.symm)
  simp only [longRangeIntervalMergeEvent, Set.mem_setOf_eq]
  have hstrict := connectedComponent_card_lt_deleteVertex_of_two_neighbors
    G 0 rV i h0r h0i hnotreach
  change Nat.card G.ConnectedComponent < Nat.card H.ConnectedComponent
  exact hstrict

theorem longRangeGeneratorEdge_mem_intervalSupport
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    longRangeGeneratorEdge r ∈ longRangeIntervalEdgeSupport
      (longRangeGeneratorIntervalBase r m + 1) := by
  rw [longRangeIntervalEdgeSupport, Finset.mem_map]
  refine ⟨s((0 : Fin (longRangeGeneratorIntervalBase r m + 2)),
      (⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩ :
        Fin (longRangeGeneratorIntervalBase r m + 2))),
    Finset.mem_univ _, ?_⟩
  simp [longRangeGeneratorEdge]

theorem dependsOn_longRangeGeneratorClosedDisconnectionEvent
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    DependsOn ((longRangeIntervalEdgeSupport
      (longRangeGeneratorIntervalBase r m + 1)).erase
      (longRangeGeneratorEdge r))
      (longRangeGeneratorClosedDisconnectionEvent r m) := by
  intro ω η h
  have hgraph : longRangeIntervalOpenGraph
      (longRangeEraseGeneratorEdge r ω)
        (longRangeGeneratorIntervalBase r m + 1) =
      longRangeIntervalOpenGraph (longRangeEraseGeneratorEdge r η)
        (longRangeGeneratorIntervalBase r m + 1) := by
    ext i j
    rw [longRangeIntervalOpenGraph_adj, longRangeIntervalOpenGraph_adj]
    apply and_congr
    · by_cases he : s((i.val : ℤ), (j.val : ℤ)) = longRangeGeneratorEdge r
      · simp [mem_longRangeEraseGeneratorEdge_iff, he]
      · rw [mem_longRangeEraseGeneratorEdge_iff,
          mem_longRangeEraseGeneratorEdge_iff]
        exact and_congr
          (h _ (Finset.mem_erase.mpr ⟨he, Finset.mem_map.mpr
            ⟨s(i, j), Finset.mem_univ _, rfl⟩⟩)) (by simp [he])
    · rfl
  change (¬(longRangeIntervalOpenGraph
      (longRangeEraseGeneratorEdge r ω)
        (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
          ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩) ↔
    ¬(longRangeIntervalOpenGraph
      (longRangeEraseGeneratorEdge r η)
        (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
          ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩
  rw [hgraph]

theorem dependsOn_longRangeGeneratorLongEdgeEvent
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    DependsOn ((longRangeIntervalEdgeSupport
      (longRangeGeneratorIntervalBase r m + 1)).erase
      (longRangeGeneratorEdge r)) (longRangeGeneratorLongEdgeEvent r m) := by
  intro ω η h
  simp only [longRangeGeneratorLongEdgeEvent, Set.mem_setOf_eq]
  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  rw [longRangeIntervalOpenGraph_adj, longRangeIntervalOpenGraph_adj]
  apply and_congr
  · apply h
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_map.mpr
      ⟨s((0 : Fin (longRangeGeneratorIntervalBase r m + 2)), i),
        Finset.mem_univ _, rfl⟩⟩
    intro he
    rcases Sym2.eq_iff.mp he with he | he <;>
      simp [longRangeGeneratorEdge] at he <;> omega
  · rfl

theorem measurableSet_longRangeGeneratorClosedDisconnectionEvent
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    MeasurableSet (longRangeGeneratorClosedDisconnectionEvent r m) :=
  (dependsOn_longRangeGeneratorClosedDisconnectionEvent hr m).measurableSet

theorem measurableSet_longRangeGeneratorLongEdgeEvent
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    MeasurableSet (longRangeGeneratorLongEdgeEvent r m) :=
  (dependsOn_longRangeGeneratorLongEdgeEvent hr m).measurableSet

theorem indepSet_longRangeGenerator_insertion
    (p : LongRangeProfile) {r : ℕ} (hr : 0 < r) (m : ℕ) :
    IndepSet
      (longRangeGeneratorClosedDisconnectionEvent r m ∩
        longRangeGeneratorLongEdgeEvent r m)
      {ω | longRangeGeneratorEdge r ∈ ω} (longRangeMeasure p) := by
  change IndepSet _ _ (inhomogeneousSetBernoulli (longRangeEdgeDensity p))
  apply inhomogeneousSetBernoulli_indepSet_of_dependsOn
    (E := (longRangeIntervalEdgeSupport
      (longRangeGeneratorIntervalBase r m + 1)).erase (longRangeGeneratorEdge r))
    (F := {longRangeGeneratorEdge r})
  · simp
  · exact (dependsOn_longRangeGeneratorClosedDisconnectionEvent hr m).inter
      (dependsOn_longRangeGeneratorLongEdgeEvent hr m)
  · intro ω η h
    exact h (longRangeGeneratorEdge r) (by simp)

theorem longRange_generatorDensity_mul_insertionEvent_le_merge
    (p : LongRangeProfile) {r : ℕ} (hr : 0 < r) (m : ℕ) :
    (p r : ℝ) * (longRangeMeasure p).real
        (longRangeGeneratorClosedDisconnectionEvent r m ∩
          longRangeGeneratorLongEdgeEvent r m) ≤
      (longRangeMeasure p).real (longRangeIntervalMergeEvent (r + m - 1)) := by
  have hind := (indepSet_longRangeGenerator_insertion p hr m).measure_inter_eq_mul
  have hindReal : (longRangeMeasure p).real
      ((longRangeGeneratorClosedDisconnectionEvent r m ∩
        longRangeGeneratorLongEdgeEvent r m) ∩
        {ω | longRangeGeneratorEdge r ∈ ω}) =
      (longRangeMeasure p).real
          (longRangeGeneratorClosedDisconnectionEvent r m ∩
            longRangeGeneratorLongEdgeEvent r m) *
        (longRangeMeasure p).real {ω | longRangeGeneratorEdge r ∈ ω} := by
    simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hind
  have hopen : (longRangeMeasure p).real
      {ω | longRangeGeneratorEdge r ∈ ω} = (p r : ℝ) := by
    rw [longRangeMeasure_real_edgeOpen]
    simp [longRangeGeneratorEdge, longRangeEdgeDensity, hr.ne']
  rw [mul_comm, ← hopen, ← hindReal]
  exact measureReal_mono (longRangeGenerator_insertion_subset_merge hr m)

/-! ### Long-edge product and finite disconnection bound -/

def longRangeGeneratorLongEdges (r m : ℕ) : Finset (Sym2 ℤ) :=
  (Finset.range m).image fun j ↦ longRangeOriginEdge (r + j, true)

theorem longRangeOriginEdge_true_add_injective (r : ℕ) :
    Function.Injective (fun j : ℕ ↦ longRangeOriginEdge (r + j, true)) := by
  intro a b hab
  have hstep := longRangeOriginEdge_injective hab
  have hfst := congrArg Prod.fst hstep
  simp at hfst
  omega

theorem longRangeGeneratorLongEdgeEvent_eq
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    longRangeGeneratorLongEdgeEvent r m =
      {ω | ∃ e ∈ longRangeGeneratorLongEdges r m, e ∈ ω} := by
  ext ω
  simp only [longRangeGeneratorLongEdgeEvent, longRangeGeneratorLongEdges,
    Set.mem_setOf_eq, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, h0i⟩
    refine ⟨longRangeOriginEdge (i.val - 1, true), ?_, ?_⟩
    · refine ⟨i.val - r - 1, by
        have hil : i.val < r + m - 1 + 2 := by
          simpa only [longRangeGeneratorIntervalBase] using i.isLt
        omega, ?_⟩
      have hidx : r + (i.val - r - 1) = i.val - 1 := by omega
      rw [hidx]
    · rw [longRangeIntervalOpenGraph_adj] at h0i
      have hedge : longRangeOriginEdge (i.val - 1, true) =
          s(((0 : Fin (longRangeGeneratorIntervalBase r m + 2)).val : ℤ),
            (i.val : ℤ)) := by
        apply Sym2.eq_iff.mpr
        left
        constructor
        · rfl
        · norm_num [longRangeOriginEdge, longRangeStepDisplacement,
            Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
      rw [hedge]
      exact h0i.1
  · rintro ⟨e, ⟨j, hj, rfl⟩, he⟩
    let i : Fin (longRangeGeneratorIntervalBase r m + 2) :=
      ⟨r + j + 1, by simp [longRangeGeneratorIntervalBase]; omega⟩
    refine ⟨i, by simp [i], ?_⟩
    rw [longRangeIntervalOpenGraph_adj]
    constructor
    · convert he using 1
    · apply Fin.ne_of_val_ne
      simp [i, hr.ne']

theorem longRangeMeasure_real_generatorLongEdge_compl
    (p : LongRangeProfile) {r : ℕ} (hr : 0 < r) (m : ℕ) :
    (longRangeMeasure p).real (longRangeGeneratorLongEdgeEvent r m)ᶜ =
      ∏ j ∈ Finset.range m, (1 - (p (r + j + 1) : ℝ)) := by
  rw [longRangeGeneratorLongEdgeEvent_eq hr]
  have hcompl : ({ω | ∃ e ∈ longRangeGeneratorLongEdges r m, e ∈ ω} :
      Set LongRangeConfiguration)ᶜ =
      {ω | Disjoint (longRangeGeneratorLongEdges r m : Set (Sym2 ℤ)) ω} := by
    ext ω
    simp [Set.disjoint_left]
  rw [hcompl, longRangeMeasure_real_disjoint_finset,
    longRangeGeneratorLongEdges, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro j _hj
    rw [longRangeEdgeDistance_originEdge]
  · intro a _ha b _hb hab
    exact longRangeOriginEdge_true_add_injective r hab

theorem longRange_generatorClosedLongEdgeProduct_tendsto_zero
    (p : LongRangeProfile) (r : ℕ)
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    Tendsto (fun m : ℕ ↦
      ∏ j ∈ Finset.range m, (1 - (p (r + j + 1) : ℝ))) atTop (nhds 0) := by
  have htail : ¬Summable fun j : ℕ ↦ (p (j + (r + 1)) : ℝ) := by
    intro hs
    apply hdiv
    exact (summable_nat_add_iff (r + 1)).mp hs
  have hsum : Tendsto (fun m : ℕ ↦
      ∑ j ∈ Finset.range m, (p (j + (r + 1)) : ℝ)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun j ↦ unitInterval.nonneg (p (j + (r + 1))))).mp htail
  have hexp : Tendsto (fun m : ℕ ↦ Real.exp
      (-(∑ j ∈ Finset.range m, (p (j + (r + 1)) : ℝ)))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsum)
  apply squeeze_zero
  · intro m
    exact Finset.prod_nonneg fun j _hj ↦
      sub_nonneg.mpr (unitInterval.le_one (p (r + j + 1)))
  · intro m
    calc
      ∏ j ∈ Finset.range m, (1 - (p (r + j + 1) : ℝ)) ≤
          ∏ j ∈ Finset.range m, Real.exp (-(p (r + j + 1) : ℝ)) := by
        apply Finset.prod_le_prod
        · intro j _hj
          exact sub_nonneg.mpr (unitInterval.le_one _)
        · intro j _hj
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-(∑ j ∈ Finset.range m,
          (p (j + (r + 1)) : ℝ))) := by
        rw [← Real.exp_sum]
        rw [Finset.sum_neg_distrib]
        congr 2
        apply Finset.sum_congr rfl
        intro j _hj
        congr 2
        omega
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hexp

theorem longRangeGeneratorDisconnection_subset_closed
    {r : ℕ} (hr : 0 < r) (m : ℕ) :
    longRangeGeneratorDisconnectionEvent r m ⊆
      longRangeGeneratorClosedDisconnectionEvent r m := by
  intro ω hdis
  change ¬(longRangeIntervalOpenGraph ω
    (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
      ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩ at hdis
  change ¬(longRangeIntervalOpenGraph
    (longRangeEraseGeneratorEdge r ω)
      (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
        ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩
  intro herased
  apply hdis
  apply herased.mono
  intro i j hij
  rw [longRangeIntervalOpenGraph_adj] at hij ⊢
  exact ⟨(mem_longRangeEraseGeneratorEdge_iff.mp hij.1).1, hij.2⟩

theorem longRangeGeneratorClosedDisconnection_subset_split (r m : ℕ) :
    longRangeGeneratorClosedDisconnectionEvent r m ⊆
      (longRangeGeneratorClosedDisconnectionEvent r m ∩
        longRangeGeneratorLongEdgeEvent r m) ∪
      (longRangeGeneratorLongEdgeEvent r m)ᶜ := by
  intro ω hdis
  by_cases hlong : ω ∈ longRangeGeneratorLongEdgeEvent r m
  · exact Or.inl ⟨hdis, hlong⟩
  · exact Or.inr hlong

theorem longRange_generatorDensity_mul_disconnection_le
    (p : LongRangeProfile) {r : ℕ} (hr : 0 < r) (m : ℕ) :
    (p r : ℝ) * (longRangeMeasure p).real
        (longRangeGeneratorDisconnectionEvent r m) ≤
      (longRangeMeasure p).real (longRangeIntervalMergeEvent (r + m - 1)) +
        (longRangeMeasure p).real (longRangeGeneratorLongEdgeEvent r m)ᶜ := by
  let A := longRangeGeneratorClosedDisconnectionEvent r m
  let B := longRangeGeneratorLongEdgeEvent r m
  have hactual : (longRangeMeasure p).real (longRangeGeneratorDisconnectionEvent r m) ≤
      (longRangeMeasure p).real A :=
    measureReal_mono (longRangeGeneratorDisconnection_subset_closed hr m)
  have hsplit : (longRangeMeasure p).real A ≤
      (longRangeMeasure p).real (A ∩ B) + (longRangeMeasure p).real Bᶜ := by
    calc
      (longRangeMeasure p).real A ≤
          (longRangeMeasure p).real ((A ∩ B) ∪ Bᶜ) :=
        measureReal_mono (longRangeGeneratorClosedDisconnection_subset_split r m)
      _ ≤ _ := measureReal_union_le _ _
  have hinsert := longRange_generatorDensity_mul_insertionEvent_le_merge p hr m
  have hp0 : (0 : ℝ) ≤ p r := unitInterval.nonneg _
  have hp1 : (p r : ℝ) ≤ 1 := unitInterval.le_one _
  have hmulActual := mul_le_mul_of_nonneg_left hactual hp0
  have hmulSplit := mul_le_mul_of_nonneg_left hsplit hp0
  have htailNonneg : (0 : ℝ) ≤ (longRangeMeasure p).real Bᶜ := measureReal_nonneg
  have htailMul : (p r : ℝ) * (longRangeMeasure p).real Bᶜ ≤
      (longRangeMeasure p).real Bᶜ := by nlinarith
  dsimp [A, B] at hactual hsplit hinsert hmulActual hmulSplit htailMul ⊢
  nlinarith

theorem longRangeGeneratorDisconnection_antitone (r : ℕ) :
    Antitone (longRangeGeneratorDisconnectionEvent r) := by
  intro m n hmn ω hn
  change ¬(longRangeIntervalOpenGraph ω
    (longRangeGeneratorIntervalBase r n + 1)).Reachable 0
      ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩ at hn
  change ¬(longRangeIntervalOpenGraph ω
    (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
      ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩
  intro hm
  have hsize : longRangeGeneratorIntervalBase r m + 2 ≤
      longRangeGeneratorIntervalBase r n + 2 := by
    simp [longRangeGeneratorIntervalBase]
    omega
  let F : longRangeIntervalOpenGraph ω (longRangeGeneratorIntervalBase r m + 1) →g
      longRangeIntervalOpenGraph ω (longRangeGeneratorIntervalBase r n + 1) := {
    toFun := Fin.castLE hsize
    map_rel' := by
      intro i j hij
      rw [longRangeIntervalOpenGraph_adj] at hij ⊢
      simpa using hij
  }
  have hmapped := hm.map F
  exact hn (by simpa [F] using hmapped)

/-- Every positive supported generator connects to the origin almost surely when the total
intensity diverges. -/
theorem longRangeMeasure_real_generatorConnection_eq_one
    (p : LongRangeProfile) {r : ℕ} (hr : 0 < r) (hpr : 0 < (p r : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    (longRangeMeasure p).real (longRangeConnectionEvent 0 (r : ℤ)) = 1 := by
  have htail : Tendsto (fun m ↦ (longRangeMeasure p).real
      (longRangeGeneratorLongEdgeEvent r m)ᶜ) atTop (nhds 0) := by
    simpa only [longRangeMeasure_real_generatorLongEdge_compl p hr] using
      longRange_generatorClosedLongEdgeProduct_tendsto_zero p r hdiv
  have hfinite : Tendsto (fun m ↦ (longRangeMeasure p).real
      (longRangeGeneratorDisconnectionEvent r m)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let delta : ℝ := (p r : ℝ) * epsilon / 4
    have hdelta : 0 < delta := by positivity
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 htail delta hdelta
    obtain ⟨k, hk, hdrop⟩ :=
      exists_large_integral_componentCount_drop_lt p hdelta (M + r)
    let m := k + 1 - r
    have hmM : M ≤ m := by dsimp [m]; omega
    have hindex : r + m - 1 = k := by dsimp [m]; omega
    have htailm : (longRangeMeasure p).real
        (longRangeGeneratorLongEdgeEvent r m)ᶜ < delta := by
      have := hM m hmM
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
    have hisolated : (longRangeMeasure p).real
        (longRangeIntervalZeroIsolatedEvent (r + m - 1)) ≤
        (longRangeMeasure p).real (longRangeGeneratorLongEdgeEvent r m)ᶜ := by
      have hsubset : longRangeIntervalZeroIsolatedEvent (r + m - 1) ⊆
          (longRangeGeneratorLongEdgeEvent r m)ᶜ := by
        intro ω hiso hlong
        rcases hlong with ⟨i, _hi, h0i⟩
        apply hiso i
        rw [longRangeIntervalOpenGraph_adj] at h0i ⊢
        simpa [longRangeGeneratorIntervalBase] using h0i
      exact measureReal_mono (μ := longRangeMeasure p) hsubset
    have hmerge := longRangeMeasure_real_merge_le_integral_sub_add_isolated
      p (r + m - 1)
    rw [hindex] at hmerge
    rw [hindex] at hisolated
    have hprob := longRange_generatorDensity_mul_disconnection_le p hr m
    rw [hindex] at hprob
    have hsmall : (longRangeMeasure p).real
        (longRangeGeneratorDisconnectionEvent r m) < epsilon := by
      have hnonneg : (0 : ℝ) ≤ (longRangeMeasure p).real
          (longRangeGeneratorDisconnectionEvent r m) := measureReal_nonneg
      dsimp [delta] at hdrop htailm ⊢
      nlinarith
    refine ⟨m, ?_⟩
    intro n hmn
    have hmono := measureReal_mono (μ := longRangeMeasure p)
      (longRangeGeneratorDisconnection_antitone r hmn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    exact hmono.trans_lt hsmall
  let D : Set LongRangeConfiguration := ⋂ m, longRangeGeneratorDisconnectionEvent r m
  have hDmeas : MeasurableSet D := by
    apply MeasurableSet.iInter
    intro m
    exact measurableSet_longRangeGeneratorDisconnectionEvent r m
  have hmeasure : Tendsto (fun m ↦ longRangeMeasure p
      (longRangeGeneratorDisconnectionEvent r m)) atTop
      (nhds (longRangeMeasure p D)) := by
    exact tendsto_measure_iInter_atTop
      (fun m ↦ (measurableSet_longRangeGeneratorDisconnectionEvent r m).nullMeasurableSet)
      (longRangeGeneratorDisconnection_antitone r) ⟨0, measure_ne_top _ _⟩
  have hreal : Tendsto (fun m ↦ (longRangeMeasure p).real
      (longRangeGeneratorDisconnectionEvent r m)) atTop
      (nhds ((longRangeMeasure p).real D)) := by
    simpa [Measure.real, D] using
      (ENNReal.tendsto_toReal (measure_ne_top (longRangeMeasure p) D)).comp hmeasure
  have hDzero : (longRangeMeasure p).real D = 0 := tendsto_nhds_unique hreal hfinite
  have hcompl : (longRangeConnectionEvent 0 (r : ℤ))ᶜ ⊆ D := by
    intro ω hconn
    rw [Set.mem_iInter]
    intro m
    change ¬(longRangeIntervalOpenGraph ω
      (longRangeGeneratorIntervalBase r m + 1)).Reachable 0
        ⟨r, by simp [longRangeGeneratorIntervalBase]; omega⟩
    intro hreach
    apply hconn
    apply longRangeOpenGraph_reachable_iff.mp
    let F : longRangeIntervalOpenGraph ω
        (longRangeGeneratorIntervalBase r m + 1) →g longRangeOpenGraph ω := {
      toFun := fun i ↦ (i.val : ℤ)
      map_rel' := by
        intro i j hij
        rw [longRangeIntervalOpenGraph_adj] at hij
        exact longRangeOpenGraph_adj.mpr ⟨hij.1, by
          intro hval
          exact hij.2 (Fin.ext (Int.ofNat_inj.mp hval))⟩
    }
    simpa [F] using hreach.map F
  have hcomplzero : (longRangeMeasure p).real
      (longRangeConnectionEvent 0 (r : ℤ))ᶜ = 0 := by
    exact le_antisymm ((measureReal_mono hcompl).trans_eq hDzero) measureReal_nonneg
  rw [measureReal_compl (measurableSet_longRangeConnectionEvent 0 r), probReal_univ]
    at hcomplzero
  linarith

/-! ### Aperiodic support and the full Theorem 12.3 -/

/-- Displacements that are connected from every translate in a fixed configuration. -/
def longRangeReachableTranslationSubgroup (ω : LongRangeConfiguration) : AddSubgroup ℤ where
  carrier := {z | ∀ x, (longRangeOpenGraph ω).Reachable x (x + z)}
  zero_mem' := fun x ↦ by simp
  add_mem' := by
    intro a b ha hb x
    convert (ha x).trans (hb (x + a)) using 1 <;> ring
  neg_mem' := by
    intro a ha x
    have h := (ha (x - a)).symm
    convert h using 1 <;> ring

theorem longRangeMeasure_real_generatorConnection_eq_one_at
    (p : LongRangeProfile) {r : ℕ} (hr : 0 < r) (hpr : 0 < (p r : ℝ))
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) (x : ℤ) :
    (longRangeMeasure p).real (longRangeConnectionEvent x (x + r)) = 1 := by
  calc
    (longRangeMeasure p).real (longRangeConnectionEvent x (x + r)) =
        (longRangeMeasure p).real
          (longRangeTranslatedEvent x (longRangeConnectionEvent 0 r)) := by
      simpa [add_comm, add_left_comm, add_assoc] using congrArg
        (fun A ↦ (longRangeMeasure p).real A)
        (longRangeTranslatedEvent_connectionEvent x 0 r).symm
    _ = (longRangeMeasure p).real (longRangeConnectionEvent 0 r) :=
      longRangeMeasure_real_translatedEvent p
        (measurableSet_longRangeConnectionEvent 0 r) x
    _ = 1 := longRangeMeasure_real_generatorConnection_eq_one p hr hpr hdiv

theorem longRange_ae_all_supported_generators_connected
    (p : LongRangeProfile) (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    ∀ᵐ ω ∂longRangeMeasure p, ∀ n : ℕ, 0 < n → 0 < (p n : ℝ) →
      ∀ x : ℤ, ω ∈ longRangeConnectionEvent x (x + n) := by
  have hnx : ∀ n : ℕ, ∀ x : ℤ, ∀ᵐ ω ∂longRangeMeasure p,
      0 < n → 0 < (p n : ℝ) →
        ω ∈ longRangeConnectionEvent x (x + n) := by
    intro n x
    by_cases hn : 0 < n
    · by_cases hpn : 0 < (p n : ℝ)
      · filter_upwards [ae_mem_of_measureReal_eq_one (longRangeMeasure p)
          (measurableSet_longRangeConnectionEvent x (x + n))
          (longRangeMeasure_real_generatorConnection_eq_one_at p hn hpn hdiv x)] with ω hω
        exact fun _ _ ↦ hω
      · filter_upwards [] with ω
        exact fun _ h ↦ (hpn h).elim
    · filter_upwards [] with ω
      exact fun h _ ↦ (hn h).elim
  filter_upwards [ae_all_iff.mpr fun n ↦ ae_all_iff.mpr (hnx n)] with ω hω
  intro n hn hpn x
  exact hω n x hn hpn

theorem longRange_connected_of_supported_generators_of_aperiodic
    (p : LongRangeProfile) { ω : LongRangeConfiguration }
    (hgen : ∀ n : ℕ, 0 < n → 0 < (p n : ℝ) →
      ∀ x : ℤ, ω ∈ longRangeConnectionEvent x (x + n))
    (haper : p.IsAperiodic) : ω ∈ longRangeConnectedEvent := by
  have hsupp : longRangePositiveStepSet p ⊆
      longRangeReachableTranslationSubgroup ω := by
    intro z hz
    rcases hz with ⟨hz0, hzp⟩
    have hnpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz0
    have hpos : (z.natAbs : ℤ) ∈ longRangeReachableTranslationSubgroup ω := by
      intro x
      exact longRangeOpenGraph_reachable_iff.mpr
        (hgen z.natAbs hnpos hzp x)
    rcases z with z | z
    · simpa using hpos
    · have hneg := (longRangeReachableTranslationSubgroup ω).neg_mem hpos
      have heq : -((Int.negSucc z).natAbs : ℤ) = Int.negSucc z := by
        rw [Int.natCast_natAbs, abs_of_neg (Int.negSucc_lt_zero z)]
        rw [Int.negSucc_eq]
        ring
      rw [← heq]
      exact hneg
  have hclosure : longRangeSupportSubgroup p ≤
      longRangeReachableTranslationSubgroup ω :=
    (AddSubgroup.closure_le _).mpr hsupp
  have htop : longRangeReachableTranslationSubgroup ω = ⊤ := by
    apply top_unique
    rw [← haper]
    exact hclosure
  rw [mem_longRangeConnectedEvent_iff]
  intro x y
  have hdisp : y - x ∈ longRangeReachableTranslationSubgroup ω := by
    rw [htop]
    trivial
  have hreach := hdisp x
  convert longRangeOpenGraph_reachable_iff.mp hreach using 1 <;> ring

/-- Sufficiency in Grimmett's Theorem 12.3, with no nearest-neighbour normalization. -/
theorem longRange_ae_connected_of_aperiodic_of_not_summable
    (p : LongRangeProfile) (haper : p.IsAperiodic)
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    ∀ᵐ ω ∂longRangeMeasure p, ω ∈ longRangeConnectedEvent := by
  filter_upwards [longRange_ae_all_supported_generators_connected p hdiv] with ω hgen
  exact longRange_connected_of_supported_generators_of_aperiodic p hgen haper

theorem longRangeConnectedProbability_eq_one_of_aperiodic_of_not_summable
    (p : LongRangeProfile) (haper : p.IsAperiodic)
    (hdiv : ¬Summable fun n : ℕ ↦ (p n : ℝ)) :
    longRangeConnectedProbability p = 1 := by
  have hae := longRange_ae_connected_of_aperiodic_of_not_summable p haper hdiv
  have hm : longRangeMeasure p longRangeConnectedEvent =
      longRangeMeasure p Set.univ :=
    (ae_mem_iff_measure_eq measurableSet_longRangeConnectedEvent.nullMeasurableSet).mp hae
  rw [longRangeConnectedProbability, measureReal_def, hm]
  simp

/-- **Grimmett, Theorem 12.3.** Under the source convention `pₙ<1`, the long-range graph is
connected almost surely exactly when its support is aperiodic and its total intensity diverges. -/
theorem longRange_ae_connected_iff
    (p : LongRangeProfile) (hp : p.IsStrict) :
    (∀ᵐ ω ∂longRangeMeasure p, ω ∈ longRangeConnectedEvent) ↔
      p.IsAperiodic ∧ ¬Summable fun n : ℕ ↦ (p n : ℝ) := by
  constructor
  · intro hconn
    constructor
    · have hboth : ∀ᵐ ω ∂longRangeMeasure p,
          ω ∈ longRangeConnectedEvent ∧
            ω ∈ longRangeRespectsProfileEvent p := by
        filter_upwards [hconn, longRange_ae_respectsProfile p] with ω hc hr
        exact ⟨hc, hr⟩
      obtain ⟨ω, hωc, hωr⟩ := hboth.exists
      exact p.isAperiodic_of_connected_of_respectsProfile hωc hωr
    · intro hsum
      have hprobOne : longRangeConnectedProbability p = 1 := by
        have hm : longRangeMeasure p longRangeConnectedEvent =
            longRangeMeasure p Set.univ :=
          (ae_mem_iff_measure_eq
            measurableSet_longRangeConnectedEvent.nullMeasurableSet).mp hconn
        rw [longRangeConnectedProbability, measureReal_def, hm]
        simp
      exact (ne_of_lt (longRangeConnectedProbability_lt_one_of_summable p hp hsum)) hprobOne
  · rintro ⟨haper, hdiv⟩
    exact longRange_ae_connected_of_aperiodic_of_not_summable p haper hdiv

theorem longRangeConnectedProbability_eq_one_iff
    (p : LongRangeProfile) (hp : p.IsStrict) :
    longRangeConnectedProbability p = 1 ↔
      p.IsAperiodic ∧ ¬Summable fun n : ℕ ↦ (p n : ℝ) := by
  rw [← longRange_ae_connected_iff p hp]
  constructor
  · intro hprob
    exact ae_mem_of_measureReal_eq_one (longRangeMeasure p)
      measurableSet_longRangeConnectedEvent hprob
  · intro hae
    have hm : longRangeMeasure p longRangeConnectedEvent =
        longRangeMeasure p Set.univ :=
      (ae_mem_iff_measure_eq measurableSet_longRangeConnectedEvent.nullMeasurableSet).mp hae
    rw [longRangeConnectedProbability, measureReal_def, hm]
    simp

end Percolation
